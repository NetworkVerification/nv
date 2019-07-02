open Collections
module T = ANSITerminal

type file_info = {input: string array; linenums: (int * int) array}

type info = file_info StringMap.t

let show_message msg color label =
  T.print_string [] "\n" ;
  T.print_string [T.Foreground color; T.Bold] (label ^ ": ") ;
  Printf.printf "%s" msg ;
  T.print_string [] "\n"

let error msg =
  show_message msg T.Red "error" ;
  exit 0

let warning msg = show_message msg T.Yellow "warning"

let read_files fnames : info =
  let read_one_file fname =
    let lines = ref [] in
    let indices = ref [] in
    let index = ref 0 in
    let chan =
      try open_in fname with _ ->
        error (Printf.sprintf "file '%s' not found" fname)
    in
    try
      while true do
        let line = input_line chan in
        let len = String.length line in
        let new_len = !index + len + 1 in
        indices := (!index, new_len) :: !indices ;
        index := new_len ;
        lines := line :: !lines
      done ;
      {input= Array.of_list !lines; linenums= Array.of_list !indices}
    with End_of_file ->
      close_in chan ;
      { input= Array.of_list (List.rev !lines)
      ; linenums= Array.of_list (List.rev !indices) }
  in
  List.fold_left
    (fun acc fname -> StringMap.add fname (read_one_file fname) acc)
    StringMap.empty
    fnames

let get_position_opt fname idx info =
  let position = ref None in
  if fname = "" then None else
    let file_info = StringMap.find fname info in
    Array.iteri
      (fun i (s, e) ->
         if idx >= s && idx <= e then position := Some (i, idx - s) )
      file_info.linenums ;
    !position

let get_position idx fname info =
  match get_position_opt fname idx info with
  | None -> failwith "internal error (get_position)"
  | Some x -> x

let get_start_position (span : Span.t) info = get_position_opt span.fname span.start info

let get_end_position (span : Span.t) info = get_position_opt span.fname span.finish info

let get_line idx info = (info.input).(idx)

let rec repeat s n = if n = 1 then s else s ^ repeat s (n - 1)

let show_line info line_num underline =
  let line = get_line line_num info in
  T.print_string [T.Foreground T.Blue] (string_of_int line_num) ;
  Printf.printf "|  %s\n" line ;
  match underline with
  | None -> ()
  | Some (c1, c2, color) ->
    let num_space =
      (string_of_int line_num |> String.length) + 3 + c1
    in
    Printf.printf "%s" (repeat " " num_space) ;
    T.print_string [T.Foreground color] (repeat "~" (c2 - c1)) ;
    Printf.printf "\n"

let show_message_position info (span: Span.t) msg color label =
  let border = "\n" in
  (match get_start_position span info, get_end_position span info with
   | Some (l1, c1), Some (l2, c2) ->
     let file_info = StringMap.find span.fname info in
     T.print_string [] border ;
     if l2 - l1 = 0 then show_line file_info l1 (Some (c1, c2, color))
     else for i = l1 to l2 do show_line file_info i None done ;
     T.print_string [] "\n"
   | _, _ -> ());
  T.print_string [T.Foreground color; T.Bold] (label ^ ": ") ;
  Printf.printf "%s: %s\n" span.fname msg ;
  T.print_string [] border

let error_position info span msg =
  show_message_position info span msg T.Red "error" ;
  exit 0

let warning_position info span msg =
  show_message_position info span msg T.Yellow "warning"
