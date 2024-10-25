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

let sat  =[[1;2;-3];[-3;1];[-2];[-3; -2;-1]]
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

(** [simplifie_petite_clauses] Fonction pour simplifier les clauses **)
(** @argument  le littéral avec lequel on simplifie et la clause qu'on veut simplifier
    @return [None] si la clause est vide ou qu'elle est satisfiable et la clause sans le dual du littéral sinon **)
let rec simplifie_petite_clauses l clauses = 
  match clauses with
  | [] -> Some [] 
  | a::w ->
    if a = l then None
    else if a = (-l) then simplifie_petite_clauses l w (** Si il y'a son dual alors on passe a la suite de la liste san sl'ajouter **)
    else 
      match simplifie_petite_clauses l w with
      | None -> None
      | Some rest -> Some (a :: rest) 
;;

(** [simplifie ]simplifie l'ensemble des clauses **)
(** @arguments le littéral avec lequel on simplifiera la clause et l'ensemble des clauses
    @return la liste vide si l'ensemble des clauses est vide sinon  la liste simplifié avec l **)
let rec simplifie l clauses = 
  match clauses with
  | [] -> []
  | a::clauses' -> 
    match simplifie_petite_clauses l a with (**appel de [simplifie_petite_clauses] pour chaque sous-liste **)
    | None -> simplifie l clauses' (** Si [simplifie_petite_clauses] renvoie rien alors on fais l'appel sur clauses' **)
    | Some simplified_clause -> simplified_clause :: (simplifie l clauses') (** Si [simplifie_petite_clauses] renvoie la clause simplifié alors on la concatene avec l'appel suivant  **)
;;


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  if clauses = [] then  
    Some interpretation 
  else
  if mem [] clauses then 
    None 
  else
    let l = hd (hd clauses) in
    let branche = solveur_split (simplifie l clauses) (l::interpretation) in
    match branche with
    | None -> 
      solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
    | _    -> 
      branche
;;

(* tests *)
let () = print_modele (solveur_split systeme [])
let () = print_modele (solveur_split coloriage [])

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
   - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
   - sinon, lève une exception `Failure "pas de littéral pur"' *)

exception Failure;;

(** Fonction de comparaison par rapport au valeurs absolues**)
let comp a b =
  if abs a = abs b then 0 
  else if abs a > abs b then 1
  else -1
;;

(** [sans_doublons]
    @arguments une liste l 
    @return l sans doublons **)
let rec sans_doublons l =
  match l with
  | [] -> []
  | a ::w ->
    let res = sans_doublons w in (** stock le resultat du prochain appel,  **)
    if List.mem a res then res else a::res (** si a n'est pas dans la liste on l'ajoutes sinon on retourne la liste **)

(** [pur] 
    @arguments la liste des clauses  
    @return Un élément pur si il existe et lève une exception sinon **)
let pur clauses = 
  let flat = List.flatten clauses in (* Renvoie la liste applati *)
  let sorted= List.sort comp flat in (* Trie la liste par rapport aux valeurs absolues *)
  let distinct = sans_doublons sorted in (* Enleve les doublons de la liste  *)
  let rec aux l = match l with  (* Fonction auxiliaire qui compare les éléments 2 à 2 *)
      [] -> raise Failure
    | [a] -> a
    | a::b::w-> if a=(-b) then aux w else a (* Si b n'est pas le dual de a alors a est pur *)
  in
  aux distinct 
;;




(* unitaire : int list list -> int
   - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
   - sinon, lève une exception `Not_found' *)
exception Not_found;;
(** [unitaire]
    @arguments une liste de clauses
    @return  la première clause unitaire trouvé et lève une exception sinon **)
let rec unitaire clauses = 
  match clauses with
    []-> raise Not_found
  |a::w -> if (List.length a) = 1 then List.nth a 0 else (unitaire w)  (* si la clause est de taille 1 alors on la retourne sinon on continue la recherche  *)
;;


(** [solveur_dpll_rec] : int list list -> int list -> int list option **)
(** @arguments clauses 
    @return une interprétation si la clause est satisfiable None sinon **)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then 
    Some interpretation
  else if mem [] clauses then 
    None
  else 
    try
      let u = unitaire clauses in (**on cherche un unitaire si on en trouve on on simplifie la clause**)
      (* if u != 0 then  *)
      let uu = simplifie u clauses in
      solveur_dpll_rec uu (u::interpretation)
    with Not_found -> 
    (* else  *)
    try 
      let p = pur clauses in (** on cherche un pur si on en trouve un on simplifie la clause**)
      (* if p != 0 then  *)
      let pp=simplifie p clauses in 
      solveur_dpll_rec pp (p::interpretation) 
    with Failure -> 
    (* else  *)
    match clauses with 
      []-> Some interpretation 
    |a::w -> match a with 
        []->None
      |b::l->
        let s=solveur_dpll_rec (simplifie b clauses) (b::interpretation)   in (** sinon on prend le premier littéral de la premiere clause et on simplifie la liste**)
        match s  with 
          None -> solveur_dpll_rec (simplifie (-b) clauses) ((-b)::interpretation) (** si on trouve pas d'interpretation on test simplifie la clause avec le dual de la premire clause**)
        |Some e -> s (**sinon on retourne l'interprétation**)
;;
(* tests *)
(* ----------------------------------------------------------- *)
let () = print_modele (solveur_dpll_rec sat []) 
let () = print_modele (solveur_dpll_rec systeme []) 
let () =print_modele(solveur_dpll_rec coloriage [])

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses []) 