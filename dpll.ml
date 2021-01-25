open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* ou : 'a option -> 'a option -> 'a option
   prendre le « ou » de deux options *)
let ou a b =
  match a with
  | None -> b
  | _    -> a

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_13 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let accessibilite = [[-1;2];[-1;7];[-2;1];[-2;3];[-3;2];[-3;4];[-4;5];[-4;15];[-5;2];[-5;4];[-6;5];[-7;1];[-7;8];[-7;6];[-8;7];[-8;9];[-8;10];[-9;8];[-10;8];[-10;11];[-10;12];[-11;9];[-11;10];[-12;6];[-12;10];[-12;13];[-12;15];[-13;11];[-14;13];[-14;15];[-15;12];[1];[-14]]
let grammaire = [[6];[1;-2;-3;-4];[1;-2;-5];[5;-3;-5];[2;-3];[3;-4];[4;-6];[-1]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie_clause : int -> int list -> int list -> int list 
   applique la simplification d'une clause en mettant
   le littéral i à vrai *)
   
let rec simplifie_clause i clause init = match clause with 
|[] -> init
| y::t -> 
    if List.mem (-y) (init@t) then [] else  (*la on a véfirifié si cette clause contient y et -y pour la supprimer*) 
    if y=i then []
    else if y=(-i)  then let var=init@t in if var==[] then [0] else var      
    else simplifie_clause i t (y::init)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)

let simplifie i clauses = 
  let rec aux i clauses acc =
    match clauses with
    | [] ->acc
    | clause::l -> let c = (simplifie_clause i clause []) in 
      match c with  
        | [] -> aux i l acc  
        | [0] ->aux i l ([]::acc) 
        | _ -> aux i l (c::acc)  
    in aux i clauses []
(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

let rec unitaire clauses = match clauses with
| [] -> raise Not_found
| x::l -> match x with 
  |[y] -> y
  |_ -> unitaire l
    
(* get_proposition : 'a list list -> 'a list -> 'a list
  fonction pour avoir une liste de toutes les propositions dans les clauses
 *)

let rec get_proposition clauses init = 
  match clauses with 
    | [] -> init
    | x::l -> match x with 
      | [] -> get_proposition l init
      | y::t -> if mem y init 
        then get_proposition (t::l) init
        else get_proposition (t::l) (y::init)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
    exception Failure of string
    let pur clauses =
      let prop = (get_proposition clauses []) in  
      let rec purP propositions p =  
        match propositions with
          | [] -> raise (Failure "pas de littéral pur")
          | x::l -> if not (mem (-x) p) then x else purP l p  
      in purP prop prop

(* getProp : int list list -> int
 fonction choisir la proposition pour simplfier les clauses avec  test s'il ya une prop unitaire si non prop pure si non choisir une autre propo*)

let getProp clauses =
  try (unitaire clauses) 
  with Not_found ->try (pur clauses) 
  with Failure "pas de littéral pur"-> (nth (nth clauses 0) 0)

(* solveur_dpll_rec : int list list -> int list -> int list option *)

let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation else
  if mem [] clauses then None else
  let p = getProp clauses in
  let a=solveur_dpll_rec (simplifie p clauses) (p::interpretation) in 
  match a with
    | None -> solveur_dpll_rec (simplifie (-p) clauses) ((-p)::interpretation)
    | _    -> a

(* tests *)
(* let () = print_modele (solveur_dpll_rec accessibilite []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)
(* let () = print_modele (solveur_dpll_rec grammaire []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
