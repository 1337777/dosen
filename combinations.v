
Require Import List.
Import ListNotations.

Definition enumerate {A :Set} (data : list A) (heights : list nat) : list (list (list A)) :=
  let enumerate := 
      (fix  enumerate data heights selection combination enumeration {struct data} :=
         match data with
           | [] =>
             match heights with
	       | [] => ((List.rev combination) :: enumeration) 
	       | _ => enumeration
             end
           | x :: restData =>
             match heights with
	       | [] => ((List.rev combination) :: enumeration) 
	       | 0 :: restHeights =>
	         enumerate restData heights selection combination
	               (enumerate restData restHeights [] ((List.rev (x :: selection)) :: combination) enumeration)
	       | S curHeight :: restHeights =>
	         enumerate restData heights selection combination
		       (enumerate restData (curHeight :: restHeights) (x :: selection) combination enumeration) 
             end
         end)
  in
  enumerate data heights [] [] [].

Require Import String.
Open Scope string.

Compute List.rev ( enumerate [ "a" ; "b" ; "c" ; "d" ; "e" ; "f" ; "g" ] [ 0 ; 1 ; 0 ] ).

(**
     = [[["a"]; ["b"; "c"]; ["d"]]; [["a"]; ["b"; "c"]; ["e"]];
       [["a"]; ["b"; "c"]; ["f"]]; [["a"]; ["b"; "c"]; ["g"]];
       [["a"]; ["b"; "d"]; ["e"]]; [["a"]; ["b"; "d"]; ["f"]];
       [["a"]; ["b"; "d"]; ["g"]]; [["a"]; ["b"; "e"]; ["f"]];
       [["a"]; ["b"; "e"]; ["g"]]; [["a"]; ["b"; "f"]; ["g"]];
       [["a"]; ["c"; "d"]; ["e"]]; [["a"]; ["c"; "d"]; ["f"]];
       [["a"]; ["c"; "d"]; ["g"]]; [["a"]; ["c"; "e"]; ["f"]];
       [["a"]; ["c"; "e"]; ["g"]]; [["a"]; ["c"; "f"]; ["g"]];
       [["a"]; ["d"; "e"]; ["f"]]; [["a"]; ["d"; "e"]; ["g"]];
       [["a"]; ["d"; "f"]; ["g"]]; [["a"]; ["e"; "f"]; ["g"]];
       [["b"]; ["c"; "d"]; ["e"]]; [["b"]; ["c"; "d"]; ["f"]];
       [["b"]; ["c"; "d"]; ["g"]]; [["b"]; ["c"; "e"]; ["f"]];
       [["b"]; ["c"; "e"]; ["g"]]; [["b"]; ["c"; "f"]; ["g"]];
       [["b"]; ["d"; "e"]; ["f"]]; [["b"]; ["d"; "e"]; ["g"]];
       [["b"]; ["d"; "f"]; ["g"]]; [["b"]; ["e"; "f"]; ["g"]];
       [["c"]; ["d"; "e"]; ["f"]]; [["c"]; ["d"; "e"]; ["g"]];
       [["c"]; ["d"; "f"]; ["g"]]; [["c"]; ["e"; "f"]; ["g"]];
       [["d"]; ["e"; "f"]; ["g"]]]
     : list (list (list string))
 **)

