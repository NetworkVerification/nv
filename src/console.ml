module T = ANSITerminal

type info = {input: string array; linenums: (int * int) array}

let get_position_opt idx info =
  let position = ref None in
  Array.iteri
    (fun i (s, e) -> if idx >= s && idx <= e then position := Some (i, idx - s))
    info.linenums ;
  !position

let show_message msg color label =
  T.print_string [] "\n" ;
  T.print_string [T.Foreground color; T.Bold] (label ^ ": ") ;
  Printf.printf "%s\n" msg ;
  T.print_string [] "\n"

let error msg =
  show_message msg T.Red "error" ;
  exit 0

let warning msg = show_message msg T.Yellow "warning"

let get_position idx info =
  match get_position_opt idx info with
  | None -> error "internal error (get_position)"
  | Some x -> x

let get_line idx info = (info.input).(idx)

let rec repeat s n = if n = 1 then s else s ^ repeat s (n - 1)

let show_line info line_num underline =
  let line = get_line line_num info in
  T.print_string [T.Foreground T.Blue] (string_of_int line_num) ;
  Printf.printf "|  %s\n" line ;
  match underline with
  | None -> ()
  | Some (c1, c2, color) ->
      let num_space = (string_of_int line_num |> String.length) + 3 + c1 in
      Printf.printf "%s" (repeat " " num_space) ;
      T.print_string [T.Foreground color] (repeat "~" (c2 - c1)) ;
      Printf.printf "\n"

let show_message_position info (span: Span.t) msg color label =
  let l1, c1 = get_position span.start info in
  let l2, c2 = get_position span.finish info in
  let border = "\n" in
  T.print_string [] border ;
  if l2 - l1 = 0 then show_line info l1 (Some (c1, c2, color))
  else for i = l1 to l2 do show_line info i None done ;
  T.print_string [] "\n" ;
  T.print_string [T.Foreground color; T.Bold] (label ^ ": ") ;
  Printf.printf "%s\n" msg ;
  T.print_string [] border

let error_position info span msg =
  show_message_position info span msg T.Red "error" ;
  exit 0

let warning_position info span msg =
  show_message_position info span msg T.Yellow "warning"
