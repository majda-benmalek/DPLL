(* MP1 2024/2025 - dpll.ml *)

open List
open Dimacs 

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien y ajouter.
     Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   afficher le résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
    let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
    List.iter (fun i -> print_int i; print_string " ") modele2;
    print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]

let sat  =[[1;2;-3];[-3;1];[-2];[-3;-2;-1]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
exception Stop;; 

let rec simplifie_petite_clauses1 l clauses = 
  match clauses with
    []-> [] 
  |a::w ->
    if a=l then  raise Stop
    else if a = (-l) then simplifie_petite_clauses1 l w
    else a::simplifie_petite_clauses1 l w
;;

let simplifie_petite_clauses l clauses = 
  try
    simplifie_petite_clauses1 l clauses  (* Appel de la fonction principale *)
  with Stop ->  []  (* Si l'exception Stop est levée, on retourne une liste vide *)
;;

let rec simplifie l clauses = 
  match clauses with
  | [] -> []
  | a::clauses' -> 
    let simplified_clause = simplifie_petite_clauses l a in
    simplified_clause :: (simplifie l clauses')
;;

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* Printf.printf "Appel de split avec clauses: %s et interpretation: %s\n"
     (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses))
     (String.concat " " (List.map string_of_int interpretation)); *)

  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then  
    Some interpretation 
  else
    (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then 
    None 
  else
    (* branchement *) 
    let l = hd (hd clauses) in
    let branche = solveur_split (simplifie l clauses) (l::interpretation) in
    match branche with
    | None -> 
      (* begin
         Printf.printf "Simplification avec %d n'as pas marché avec on le fais avec %d\n\n" (l) (-l); *)
      solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
    (* end *)
    | _    -> 
      (* begin *)
      (* Printf.printf "_ de split: %s\n\n"
         (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses)); *)
      branche
(* end *)

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
   - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
   - sinon, lève une exception `Failure "pas de littéral pur"' *)
exception Failure;;
let rec aux l a = 
  try 
    match l with
      []->raise Failure 
    |[b] -> if b = (-a) then raise Failure else a
    |b::w ->  if b=(-a) then raise Failure else aux w a 
  with Failure -> 0
;;

let rec aux2 c i= 
  try 
    if i >= List.length c then raise Failure else
      let ii = List.nth c i in 
      let r = 
        let rec remove_all x l = match l with
          | [] -> []  
          | a::w -> if a = x then remove_all x w 
            else a::(remove_all x w) 
        in remove_all ii c (*enleve toute les occurence de l'element ii *)
      in
      if aux r ii = 0 then aux2 c (i + 1) else ii
  with 
  |Failure -> begin 
      (* Printf.printf "Pas de pur\n\n"; *)
      0
    end

;;
let pur clauses  = 
  (* Printf.printf "Appel de pur avec clauses: %s : \n"
     (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses)); *)
  let l = List.flatten clauses in 
  aux2 l 0
;;

(* unitaire : int list list -> int
   - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
   - sinon, lève une exception `Not_found' *)
let rec unitaire clauses = 
  (* Printf.printf "Appel de unitaire avec clauses: %s : \n"
     (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses)); *)
  try
    match clauses with
      []-> raise Not_found
    |a::w -> if (List.length a) = 1 then List.nth a 0 else (unitaire w) 
  with 
  |Not_found -> begin 
      (* Printf.printf "Pas d'unitaire \n\n"; *)
      0
    end
;;


(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* Printf.printf "Appel de solveur_dpll_rec avec clauses: %s et interpretation: %s\n"
     (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses))
     (String.concat " " (List.map string_of_int interpretation)); *)
  (* l'ensemble vide de clauses est satisfiable *)
  (* if clauses =[] then begin
     (* Printf.printf "Arrêt: toutes les sous-listes de clauses sont vides.\n"; *)
     Some interpretation
     end *)
  (* else 
     if mem [] clauses then None *)
  (* else  *)
  let u = unitaire clauses in 
  if u != 0 then 
    (* begin 
       Printf.printf "Unitaire trouvé: %d\n" u;
       Printf.printf "Ce qu'on avant de simplifier unitaire  %s\n  " 
       (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses)); *)
    let uu = simplifie u clauses in
    (* Printf.printf "Simplifie avec Unitaire %s avec %d\n" 
       (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) uu)) (u);
    *)
    solveur_dpll_rec uu (u::interpretation)
    (* end   *)
  else 
    let p = pur clauses in 
    if p != 0 then
      (* begin
         Printf.printf "Pur trouvé: %d\n" p;
         Printf.printf "Ce qu'on avant de simplifier pur %s\n  " 
         (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) clauses)); *)
      let pp=simplifie p clauses in 
      (* Printf.printf "Simplifie avec Pur %s avec %d\n " 
         (String.concat " " (List.map (fun l -> Printf.sprintf "[%s]" (String.concat " " (List.map string_of_int l))) pp)) (p); *)

      solveur_dpll_rec pp (p::interpretation)
      (* end  *)
    else 
      let split=solveur_split clauses interpretation  in
      match split with 
        None -> 
        begin 
          Printf.printf "Split renvoie None\n";
          Some interpretation
        end
      | Some e ->
        (* Printf.printf "Split: %d\n" (List.length e); *)
        solveur_dpll_rec [e] interpretation

;;
(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec sat [])  *)
(* let () = print_modele (solveur_dpll_rec coloriage [])  *)
(* let () =print_modele(solveur_dpll_rec exemple_3_12 []) *)

(* let exemple_clauses = [
   [1; -3];
   [-1; 2; 3];
   [-2; -3];
   ]

   let () = print_modele (solveur_dpll_rec exemple_clauses []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses []) 
