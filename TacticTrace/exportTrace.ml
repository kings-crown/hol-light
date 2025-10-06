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

let exptrace_dump (dir_path:string): unit =
  Sys.mkdir dir_path 0o777;
  let substract l1 l2 =
    List.filter (fun itm -> not (List.mem itm l2)) l1 in
  let string_of_asm_list l =
    (List.map (fun th -> "\"" ^ String.escaped (string_of_term (concl (snd th))) ^ "\"") l) in

  let path = dir_path ^ "/trace.json" in
  let oc = open_out path in

  Printf.fprintf oc "[\n";
  let logs = ExportTrace.get_logs () in
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
  Printf.fprintf oc "]\n";
  Printf.printf "Dumped to %s\n" path;
  close_out oc;;

(* a helper function *)
let rec to_n_elems (r:string list) n:string list =
  if n = 0 then []
  else match r with
  | h::t -> h::(to_n_elems t (n-1))
  | [] -> replicate "(unknown)" n;;


set_jrh_lexer;;
