(* This file must be loaded inside HOL Light proof files *)
(* Add typed goal serialization to exportTrace *)
unset_jrh_lexer;;
module ExportTrace = struct
  type tac_record = {
    definition_line_number: string * int;
    user_line_number: string * int;
    goal_before: goal;
    goals_after: goal list;
    num_subgoals: int;
  }

  type conv_record = {
    definition_line_number: string * int;
    user_line_number: string * int;
    input: term;
    output: thm
  }

  (* Separate record_args to lazily evaluate this (otherwise it takes too long) *)
  type record_args = {
    names: string list;
    types: string list;
    values: string list;
    exprs: string list;
  }

  (***************************************************************************)
  (*                    Monotonic, comprehensive trace store                  *)
  (***************************************************************************)

  type log_entry =
    | TacticEntry of {
        index: int;
        name: string;
        record: tac_record;
        args: record_args;
      }
    | ConversionEntry of {
        index: int;
        name: string;
        record: conv_record;
        args: record_args;
      }

  let next_index = ref 1
  let log_entries_rev : log_entry list ref = ref []

  let allocate_index () =
    let idx = !next_index in
    next_index := idx + 1;
    idx

  let add_tactic_entry (name:string) (record:tac_record) (args:record_args): unit =
    let entry =
      TacticEntry { index = allocate_index (); name; record; args } in
    log_entries_rev := entry :: !log_entries_rev

  let add_conversion_entry (name:string) (record:conv_record) (args:record_args): unit =
    let entry =
      ConversionEntry { index = allocate_index (); name; record; args } in
    log_entries_rev := entry :: !log_entries_rev

  let get_logs (): log_entry list = List.rev !log_entries_rev

  let reset_logs (): unit =
    begin
      log_entries_rev := [];
      next_index := 1
    end

  type log_state = log_entry list * int

  let snapshot_state (): log_state =
    (!log_entries_rev, !next_index)

  let restore_state ((entries, next_idx):log_state): unit =
    begin
      log_entries_rev := entries;
      next_index := next_idx
    end


end;;


exception Trace_dump_too_large of string option

let exptrace_logging_enabled = ref true

let exptrace_pause_logging (): unit = exptrace_logging_enabled := false
let exptrace_resume_logging (): unit = exptrace_logging_enabled := true


let exptrace_add_tac (tactic_name:string)
        (re:ExportTrace.tac_record)
        (re_arg_gen:unit -> ExportTrace.record_args)=
  if !exptrace_logging_enabled then
    ExportTrace.add_tactic_entry tactic_name re (re_arg_gen())
  else ()

let exptrace_add_conv (conv_name:string)
        (re:ExportTrace.conv_record)
        (re_arg_gen:unit -> ExportTrace.record_args) =
  if !exptrace_logging_enabled then
    ExportTrace.add_conversion_entry conv_name re (re_arg_gen())
  else ()

let exptrace_dump_dir : string ref = ref ""

let ensure_dir (dir_path:string): unit =
  try Sys.mkdir dir_path 0o777 with Sys_error _ -> ()

let exptrace_max_bytes : int option ref = ref None

let exptrace_set_max_bytes (limit:int option): unit =
  exptrace_max_bytes := limit

let exptrace_skip_file : string option ref = ref None
let exptrace_skipped_theorems : (string, unit) Hashtbl.t = Hashtbl.create 64

let exptrace_load_skip_list (path:string): unit =
  Hashtbl.clear exptrace_skipped_theorems;
  if Sys.file_exists path then
    In_channel.with_open_text path (fun ic ->
      try
        while true do
          let line = String.trim (input_line ic) in
          if line <> "" then Hashtbl.replace exptrace_skipped_theorems line ()
        done
      with End_of_file -> ())
  else ()

let exptrace_configure_skip_file (dir_path:string): unit =
  let path = Filename.concat dir_path "skip_theorems.txt" in
  exptrace_skip_file := Some path;
  exptrace_load_skip_list path

let exptrace_record_skipped_theorem (theorem_name:string): unit =
  if not (Hashtbl.mem exptrace_skipped_theorems theorem_name) then begin
    Hashtbl.replace exptrace_skipped_theorems theorem_name ();
    match !exptrace_skip_file with
    | Some path ->
      let oc =
        open_out_gen [Open_creat; Open_text; Open_append] 0o666 path in
      output_string oc (theorem_name ^ "\n");
      close_out oc
    | None -> ()
  end

let exptrace_theorem_is_skipped (theorem_name:string): bool =
  Hashtbl.mem exptrace_skipped_theorems theorem_name

let exptrace_set_dump_directory (dir_path:string): unit =
  exptrace_dump_dir := dir_path;
  if dir_path <> "" then exptrace_configure_skip_file dir_path

let sanitize_component (name:string): string =
  let buf = Buffer.create (String.length name) in
  String.iter (fun ch ->
      let code = Char.code ch in
      let is_alnum =
        (code >= Char.code 'a' && code <= Char.code 'z') ||
        (code >= Char.code 'A' && code <= Char.code 'Z') ||
        (code >= Char.code '0' && code <= Char.code '9') in
      if is_alnum || ch = '_' || ch = '-' then Buffer.add_char buf ch
      else Buffer.add_char buf '_') name;
  let sanitized = Buffer.contents buf in
  if sanitized = "" then "theorem" else sanitized

let trace_type_printer_name = "TacticTrace.ShowTypes"

let install_trace_type_printer (): unit =
  let printer fmt tm =
    let hop,args = strip_comb tm in
    if is_var hop && args = [] then begin
      Format.pp_print_string fmt "(";
      Format.pp_print_string fmt (name_of hop);
      Format.pp_print_string fmt ":";
      pp_print_type fmt (type_of hop);
      Format.pp_print_string fmt ")"
    end else
      raise (Failure trace_type_printer_name)
  in
  install_user_printer (trace_type_printer_name, printer)

let remove_trace_type_printer (): unit =
  try delete_user_printer trace_type_printer_name with Failure _ -> ()

let with_typed_printers (thunk: unit -> 'a): 'a =
  let old_pts = !print_types_of_subterms in
  let installed = ref false in
  let cleanup () =
    if !installed then remove_trace_type_printer ();
    print_types_of_subterms := old_pts
  in
  print_types_of_subterms := 2;
  try
    install_trace_type_printer (); installed := true;
    Fun.protect ~finally:cleanup thunk
  with exn ->
    cleanup (); raise exn

let render_goal goal =
  with_typed_printers (fun () -> Format.asprintf "%a" pp_print_goal goal)

let render_term term =
  with_typed_printers (fun () -> Format.asprintf "%a" pp_print_term term)

let render_thm thm =
  with_typed_printers (fun () -> Format.asprintf "%a" pp_print_thm thm)

let rec drop n lst =
  match n, lst with
  | 0, _ -> lst
  | _, [] -> []
  | n, _::t -> drop (n-1) t

let dump_logs_to_dir ?theorem_name (dir_path:string) (logs:ExportTrace.log_entry list): unit =
  ensure_dir dir_path;
  let path =
    let existing =
      try Array.to_list (Sys.readdir dir_path)
      with Sys_error _ -> [] in
    let prefix = "trace_" and suffix = ".json" in
    let max_idx =
      List.fold_left
        (fun acc name ->
           let prefix_len = String.length prefix and suffix_len = String.length suffix in
           if String.length name > prefix_len + suffix_len
              && String.starts_with ~prefix name
              && String.sub name (String.length name - suffix_len) suffix_len = suffix then
             let prefix_len = String.length prefix and suffix_len = String.length suffix in
             let core_len = String.length name - prefix_len - suffix_len in
             if core_len > 0 then
               let core = String.sub name prefix_len core_len in
               match int_of_string_opt core with
               | Some v when v > acc -> v
               | _ -> acc
             else acc
           else acc)
        0 existing in
    let next_idx = max_idx + 1 in
    Printf.sprintf "%s/%s%06d%s" dir_path prefix next_idx suffix
  in
  let write_json oc =
    let limit = !exptrace_max_bytes in
    let written = ref 0 in
    let ensure_capacity delta =
      match limit with
      | Some limit when !written + delta > limit ->
        raise (Trace_dump_too_large theorem_name)
      | _ -> ()
    in
    let write s =
      let len = String.length s in
      ensure_capacity len;
      output_string oc s;
      written := !written + len
    in
    let subtract l1 l2 =
      List.filter (fun itm -> not (List.mem itm l2)) l1 in
    let string_of_asm_list l =
      List.map (fun th -> "\"" ^ String.escaped (render_term (concl (snd th))) ^ "\"") l in
    let total = List.length logs in
    write "[\n";
    List.iteri (fun i entry ->
        let sep = if i + 1 = total then "" else "," in
        match entry with
        | ExportTrace.TacticEntry { index; name; record = r; args = r_args } ->
          let goal_before_str = render_goal r.goal_before in
          let goals_after_str =
            String.concat ", "
              (List.map (fun g ->
                   let goal_str = render_goal g in
                   "{\"goal\": \"" ^
                   String.escaped goal_str ^
                   "\", \"added_assumptions\": [" ^
                   String.concat ","
                     (string_of_asm_list (subtract (fst g) (fst r.goal_before))) ^
                   "], \"removed_assumptions\": [" ^
                   String.concat ","
                     (string_of_asm_list (subtract (fst r.goal_before) (fst g))) ^
                   "]}") r.goals_after) in
          write "  {\n";
          write (Printf.sprintf "    \"index\": %d,\n" index);
          write "    \"kind\": \"tactic\",\n";
          write (Printf.sprintf "    \"name\": \"%s\",\n" (String.escaped name));
          write "    \"definition_line_number\": {\n";
          write (Printf.sprintf "       \"file_path\": \"%s\",\n"
                   (String.escaped (fst r.definition_line_number)));
          write (Printf.sprintf "       \"line\": %d\n" (snd r.definition_line_number));
          write "    },\n";
          write "    \"user_line_number\": {\n";
          write (Printf.sprintf "       \"file_path\": \"%s\",\n"
                   (String.escaped (fst r.user_line_number)));
          write (Printf.sprintf "       \"line\": %d\n" (snd r.user_line_number));
          write "    },\n";
          write (Printf.sprintf "    \"arg_names\": [%s],\n"
                   (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names)));
          write (Printf.sprintf "    \"arg_types\": [%s],\n"
                   (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types)));
          write (Printf.sprintf "    \"arg_values\": [%s],\n"
                   (String.concat ", "
                      (List.map (fun s -> "\"" ^ String.escaped s ^ "\"") r_args.values)));
          (* If the source expression is a placeholder like [th]/th/(unknown),
             fall back to the rendered arg_value so downstream consumers receive
             the actual theorem text. *)
          let patched_exprs =
            List.map2
              (fun expr value ->
                 let e = String.trim expr in
                 match e with
                 | "th" | "[th]" | "(unknown)" -> value
                 | _ -> expr)
              r_args.exprs r_args.values
          in
          write (Printf.sprintf "    \"arg_exprs\": [%s],\n"
                   (String.concat ", "
                      (List.map (fun s -> "\"" ^ String.escaped s ^ "\"") patched_exprs)));
          write (Printf.sprintf "    \"goal_before\": \"%s\",\n"
                   (String.escaped goal_before_str));
          write (Printf.sprintf "    \"goals_after\": [%s],\n" goals_after_str);
          write (Printf.sprintf "    \"num_subgoals\": %d\n" r.num_subgoals);
          write ("  }" ^ sep ^ "\n")
        | ExportTrace.ConversionEntry { index; name; record = r; args = r_args } ->
          let input_str = render_term r.input in
          let output_str = render_thm r.output in
          write "  {\n";
          write (Printf.sprintf "    \"index\": %d,\n" index);
          write "    \"kind\": \"conversion\",\n";
          write (Printf.sprintf "    \"name\": \"%s\",\n" (String.escaped name));
          write "    \"definition_line_number\": {\n";
          write (Printf.sprintf "       \"file_path\": \"%s\",\n"
                   (String.escaped (fst r.definition_line_number)));
          write (Printf.sprintf "       \"line\": %d\n" (snd r.definition_line_number));
          write "    },\n";
          write "    \"user_line_number\": {\n";
          write (Printf.sprintf "       \"file_path\": \"%s\",\n"
                   (String.escaped (fst r.user_line_number)));
          write (Printf.sprintf "       \"line\": %d\n" (snd r.user_line_number));
          write "    },\n";
          write (Printf.sprintf "    \"arg_names\": [%s],\n"
                   (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names)));
          write (Printf.sprintf "    \"arg_types\": [%s],\n"
                   (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types)));
          write (Printf.sprintf "    \"arg_values\": [%s],\n"
                   (String.concat ", "
                      (List.map (fun s -> "\"" ^ String.escaped s ^ "\"") r_args.values)));
          write (Printf.sprintf "    \"arg_exprs\": [%s],\n"
                   (String.concat ", "
                      (List.map (fun s -> "\"" ^ String.escaped s ^ "\"") r_args.exprs)));
          write (Printf.sprintf "    \"input\": \"%s\",\n"
                   (String.escaped input_str));
          write (Printf.sprintf "    \"output\": \"%s\"\n"
                   (String.escaped output_str));
          write ("  }" ^ sep ^ "\n"))
      logs;
    write "]\n"
  in
  let latest = Filename.concat dir_path "trace.json" in
  let oc = open_out path in
  let finalize_main success =
    if not success then begin
      close_out_noerr oc;
      (try Sys.remove path with Sys_error _ -> ())
    end else close_out oc
  in
  (try
     write_json oc;
     finalize_main true
   with ex ->
     finalize_main false;
     raise ex);
  let oc_latest = open_out latest in
  let finalize_latest success =
    if not success then begin
      close_out_noerr oc_latest;
      (try Sys.remove latest with Sys_error _ -> ())
    end else close_out oc_latest
  in
  (try
     write_json oc_latest;
     finalize_latest true
   with ex ->
     finalize_latest false;
     raise ex);
  Printf.printf "Dumped to %s\n" path

let exptrace_dump (dir_path:string): unit =
  let effective_dir =
    if dir_path = "" then !exptrace_dump_dir
    else begin
      exptrace_set_dump_directory dir_path;
      dir_path
    end
  in
  if effective_dir = "" then
    failwith "exptrace_dump: no dump directory configured"
  else
    let logs = ExportTrace.get_logs () in
    begin
      try
        dump_logs_to_dir effective_dir logs;
        ExportTrace.reset_logs ()
      with
      | Trace_dump_too_large _ ->
        ExportTrace.reset_logs ();
        Printf.eprintf "exptrace_dump: skipped trace dump (size exceeds limit)\n"
    end

let exptrace_with_theorem (theorem_name:string) (thm_thunk:unit -> 'a): 'a =
  if exptrace_theorem_is_skipped theorem_name then
    let was_enabled = !exptrace_logging_enabled in
    (if was_enabled then exptrace_pause_logging ());
    Fun.protect
      (fun () -> thm_thunk ())
      ~finally:(fun () -> if was_enabled then exptrace_resume_logging ())
  else
    let base_dir = !exptrace_dump_dir in
    let state_before = ExportTrace.snapshot_state () in
    let before_count = List.length (ExportTrace.get_logs ()) in
    let attempt_dump () =
      if base_dir <> "" && not (exptrace_theorem_is_skipped theorem_name) then begin
        let after_logs = ExportTrace.get_logs () in
        let new_entries = drop before_count after_logs in
        if new_entries <> [] then
          let theorem_dir =
            Filename.concat base_dir (sanitize_component theorem_name) in
          try
            dump_logs_to_dir ~theorem_name theorem_dir new_entries
          with
          | Trace_dump_too_large _ ->
            ExportTrace.restore_state state_before;
            exptrace_record_skipped_theorem theorem_name;
            Printf.eprintf
              "exptrace_with_theorem: skipped dumping trace for %s (size exceeds limit)\n"
              theorem_name
      end
    in
    let result =
      try thm_thunk () with exn ->
        attempt_dump ();
        raise exn
    in
    attempt_dump ();
    result;;

(* a helper function *)
let rec to_n_elems (r:string list) n:string list =
  if n = 0 then []
  else match r with
  | h::t -> h::(to_n_elems t (n-1))
  | [] -> replicate "(unknown)" n;;

let () =
  exptrace_set_max_bytes (Some (75 * 1024 * 1024));
  match Sys.getenv_opt "TRACE_MAX_BYTES" with
  | Some raw ->
    begin match int_of_string_opt (String.trim raw) with
    | Some limit when limit > 0 ->
      exptrace_set_max_bytes (Some limit)
    | Some _ ->
      Printf.eprintf
        "TRACE_MAX_BYTES must be a positive integer; ignoring value %S\n"
        raw
    | None ->
      Printf.eprintf
        "TRACE_MAX_BYTES=%S is not an integer; ignoring\n"
        raw
    end
  | None -> ();;


set_jrh_lexer;;
