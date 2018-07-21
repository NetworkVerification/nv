open Input

module T = ANSITerminal

let rec repeat s n = 
  if n = 1 then s else s ^ (repeat s (n-1))

let error (info : Input.info) (span : Span.t) msg = 
  let (l1, c1) = Input.get_position span.start info in
  let (l2, c2) = Input.get_position span.finish info in
  let border = (repeat "-" 50) ^ "\n" in
  T.print_string [] border;
  if l2 - l1 = 0 then 
    let line = Input.get_line l1 info in
    let num_space = (string_of_int l1 |> String.length) + 3 + (c1) in
    T.print_string [T.Foreground T.Blue] (string_of_int l1);
    Printf.printf "|  %s\n" line;
    Printf.printf "%s" (repeat " " num_space);
    T.print_string [T.Foreground T.Red] (repeat "~" (c2-c1));
    Printf.printf "\n"
  else begin
    for i = l1 to l2 do
      let line = Input.get_line i info in
      T.print_string [T.Foreground T.Blue] (string_of_int i);
      Printf.printf "|  %s\n" line
    done
  end;
  T.print_string [T.Foreground T.Red] "\nerror: ";
  Printf.printf "%s\n" msg;
  T.print_string [] border;
  exit 0