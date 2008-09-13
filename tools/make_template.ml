let read_line () = 
  try
    Some (read_line ())
  with End_of_file -> None

let rec initial last_was_empty =
  match read_line () with
  | None -> ()
  | Some "(* begin thide *)" ->	thide last_was_empty
  | Some "" ->
      if not (last_was_empty) then
	print_newline ();
      initial true
  | Some line ->
      let idx = try Some (String.index line '(') with Not_found -> None in
      match idx with
        | Some idx ->
            if String.length line > idx+1 && line.[idx+1] = '*' then
              if line.[String.length line - 2] = '*' && line.[String.length line - 1] = ')' then
	        initial last_was_empty
	      else
	        comment last_was_empty
            else begin
              print_endline line;
              initial false
            end
        | None ->
	    print_endline line;
	    initial false

and comment last_was_empty =
  match read_line () with
  | None -> ()
  | Some line ->
      if String.length line >= 2 && line.[String.length line - 2] = '*'
	  && line.[String.length line - 1] = ')' then
	initial last_was_empty
      else
	comment last_was_empty

and thide last_was_empty =
  match read_line () with
  | None -> ()
  | Some "(* end thide *)" -> initial last_was_empty
  | Some _ -> thide last_was_empty

let () = initial false
