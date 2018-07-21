module T = ANSITerminal

type info = {input: string array; linenums: (int * int) array}

let get_position_opt idx info =
  let position = ref None in
  Array.iteri
    (fun i (s, e) -> if idx >= s && idx <= e then position := Some (i, idx - s))
    info.linenums ;
  !position


let get_position idx info =
  match get_position_opt idx info with
  | None -> failwith "invalid index for get_position"
  | Some x -> x


let get_line idx info = (info.input).(idx)

let rec repeat s n = if n = 1 then s else s ^ repeat s (n - 1)

let show_message_position info (span: Span.t) msg color label =
  let l1, c1 = get_position span.start info in
  let l2, c2 = get_position span.finish info in
  let border = "\n" in
  T.print_string [] border ;
  if l2 - l1 = 0 then (
    let line = get_line l1 info in
    let num_space = (string_of_int l1 |> String.length) + 3 + c1 in
    T.print_string [T.Foreground T.Blue] (string_of_int l1) ;
    Printf.printf "|  %s\n" line ;
    Printf.printf "%s" (repeat " " num_space) ;
    T.print_string [T.Foreground color] (repeat "~" (c2 - c1)) ;
    Printf.printf "\n" )
  else
    for i = l1 to l2 do
      let line = get_line i info in
      T.print_string [T.Foreground T.Blue] (string_of_int i) ;
      Printf.printf "|  %s\n" line
    done ;
  T.print_string [] "\n" ;
  T.print_string [T.Foreground color] (label ^ ": ") ;
  Printf.printf "%s\n" msg ;
  T.print_string [] border


let show_message msg color label =
  T.print_string [] "\n" ;
  T.print_string [T.Foreground color] (label ^ ": ") ;
  Printf.printf "%s\n" msg ;
  T.print_string [] "\n"


let error_position info span msg =
  show_message_position info span msg T.Red "error" ;
  exit 0


let warning_position info span msg =
  show_message_position info span msg T.Yellow "warning"


let error msg =
  show_message msg T.Red "error" ;
  exit 0


let warning msg = show_message msg T.Yellow "warning"