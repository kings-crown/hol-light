(* This file must be loaded inside HOL Light proof files *)

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


end;;


let exptrace_add_tac (tactic_name:string)
        (re:ExportTrace.tac_record)
        (re_arg_gen:unit -> ExportTrace.record_args)=
  ExportTrace.add_tactic_entry tactic_name re (re_arg_gen());;

let exptrace_add_conv (conv_name:string)
        (re:ExportTrace.conv_record)
        (re_arg_gen:unit -> ExportTrace.record_args) =
  ExportTrace.add_conversion_entry conv_name re (re_arg_gen());;

let exptrace_dump_dir : string ref = ref ""

let exptrace_set_dump_directory (dir_path:string): unit =
  exptrace_dump_dir := dir_path

let ensure_dir (dir_path:string): unit =
  try Sys.mkdir dir_path 0o777 with Sys_error _ -> ()

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

let rec drop n lst =
  match n, lst with
  | 0, _ -> lst
  | _, [] -> []
  | n, _::t -> drop (n-1) t

let dump_logs_to_dir (dir_path:string) (logs:ExportTrace.log_entry list): unit =
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
    let subtract l1 l2 =
      List.filter (fun itm -> not (List.mem itm l2)) l1 in
    let string_of_asm_list l =
      List.map (fun th -> "\"" ^ String.escaped (string_of_term (concl (snd th))) ^ "\"") l in
    Printf.fprintf oc "[\n";
    List.iteri (fun i entry ->
        let sep = if i + 1 = List.length logs then "" else "," in
        match entry with
        | ExportTrace.TacticEntry { index; name; record = r; args = r_args } ->
          Printf.fprintf oc "  {\n";
          Printf.fprintf oc "    \"index\": %d,\n" index;
          Printf.fprintf oc "    \"kind\": \"tactic\",\n";
          Printf.fprintf oc "    \"name\": \"%s\",\n" (String.escaped name);
          Printf.fprintf oc "    \"definition_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.definition_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.definition_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"user_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.user_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.user_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"arg_names\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names));
          Printf.fprintf oc "    \"arg_types\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types));
          Printf.fprintf oc "    \"arg_values\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.values));
          Printf.fprintf oc "    \"arg_exprs\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.exprs));
          Printf.fprintf oc "    \"goal_before\": \"%s\",\n"
            (String.escaped (Format.asprintf "%a" pp_print_goal r.goal_before));
          Printf.fprintf oc "    \"goals_after\": [%s],\n"
            (String.concat ", " (List.map (fun g ->
                "{\"goal\": \"" ^
                String.escaped (Format.asprintf "%a" pp_print_goal g) ^
                "\", \"added_assumptions\": [" ^
                String.concat ","
                  (string_of_asm_list (subtract (fst g) (fst r.goal_before))) ^
                "], \"removed_assumptions\": [" ^
                String.concat ","
                  (string_of_asm_list (subtract (fst r.goal_before) (fst g))) ^
                "]}")
                r.goals_after));
          Printf.fprintf oc "    \"num_subgoals\": %d\n" r.num_subgoals;
          Printf.fprintf oc "  }%s\n" sep
        | ExportTrace.ConversionEntry { index; name; record = r; args = r_args } ->
          Printf.fprintf oc "  {\n";
          Printf.fprintf oc "    \"index\": %d,\n" index;
          Printf.fprintf oc "    \"kind\": \"conversion\",\n";
          Printf.fprintf oc "    \"name\": \"%s\",\n" (String.escaped name);
          Printf.fprintf oc "    \"definition_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.definition_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.definition_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"user_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.user_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.user_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"arg_names\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names));
          Printf.fprintf oc "    \"arg_types\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types));
          Printf.fprintf oc "    \"arg_values\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.values));
          Printf.fprintf oc "    \"arg_exprs\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.exprs));
          Printf.fprintf oc "    \"input\": \"%s\",\n"
            (String.escaped (Format.asprintf "%a" pp_print_term r.input));
          Printf.fprintf oc "    \"output\": \"%s\"\n"
            (String.escaped (Format.asprintf "%a" pp_print_thm r.output));
          Printf.fprintf oc "  }%s\n" sep)
      logs;
    Printf.fprintf oc "]\n"
  in
  let oc = open_out path in
  write_json oc;
  close_out oc;
  let latest = dir_path ^ "/trace.json" in
  let oc_latest = open_out latest in
  write_json oc_latest;
  close_out oc_latest;
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
    dump_logs_to_dir effective_dir logs

let exptrace_with_theorem (theorem_name:string) (thm_thunk:unit -> 'a): 'a =
  let base_dir = !exptrace_dump_dir in
  let before_count = List.length (ExportTrace.get_logs ()) in
  let result =
    try thm_thunk () with exn ->
      let after_logs = ExportTrace.get_logs () in
      if base_dir <> "" then begin
        let new_entries = drop before_count after_logs in
        if new_entries <> [] then
          let theorem_dir = base_dir ^ "/" ^ sanitize_component theorem_name in
          dump_logs_to_dir theorem_dir new_entries
      end;
      raise exn
  in
  if base_dir <> "" then begin
    let after_logs = ExportTrace.get_logs () in
    let new_entries = drop before_count after_logs in
    if new_entries <> [] then
      let theorem_dir = base_dir ^ "/" ^ sanitize_component theorem_name in
      dump_logs_to_dir theorem_dir new_entries
  end;
  result;;

(* a helper function *)
let rec to_n_elems (r:string list) n:string list =
  if n = 0 then []
  else match r with
  | h::t -> h::(to_n_elems t (n-1))
  | [] -> replicate "(unknown)" n;;


set_jrh_lexer;;
