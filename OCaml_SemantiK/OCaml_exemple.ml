      (** **********************************************************)
      (** *     TP - Sémantique des langages de programmation      *)
      (** **********************************************************)

(** *******************************************)
(** ** EXERCICE 1 : Expressions arithmétiques *)
(** *******************************************)

(** Type des expressions arithmétiques *)
type 'a exp_arith =
  | Ent of int
  | Var of 'a
  | Plus  of 'a exp_arith * 'a exp_arith
  | Moins of 'a exp_arith * 'a exp_arith
  | Fois  of 'a exp_arith * 'a exp_arith
  | Div   of 'a exp_arith * 'a exp_arith

(** ********************************)
(** *** Sémantique dénotationnelle *)
(** ********************************)

(** Type des valeurs de retour *)
type valeur = Z of int | Err

(** Type des valuations *)
type 'a valuation = 'a -> int

(** *****************)
(** **** Question 1 *)
(** *****************)

(** (<+>)
    @param : a et b sont de type "valeur"
    
    @return : * un "Z of int" correspondant à la somme de a et b, 
                  si ils sont tous les 2 entiers;
              * Err, sinon 
*)               
let (<+>) a b = match (a, b) with
  | Z x, Z y -> Z (x + y)
  | _ -> Err

(** *****************)
(** **** Question 2 *)
(** *****************)
       
(** (<->)
    @param : a et b sont de type "valeur"
    
    @return : * un "Z of int" correspondant à la soustraction de a et b, 
                  si ils sont tous les 2 entiers;
              * Err, sinon 
*) 
let (<->) a b = match (a, b) with
  | Z x, Z y -> Z (x - y)
  | _ -> Err
       
(** (<*>)
    @param : a et b sont de type "valeur"
    
    @return : * un "Z of int" correspondant à la multiplication de a et b, 
                  si ils sont tous les 2 entiers;
              * Err, sinon 
*) 
let (<*>) a b = match (a, b) with
  | Z x, Z y -> Z (x * y)
  | _ -> Err
       
(** (</>)
    @param : a et b sont de type "valeur"
    
    @return : * un entier correspondant à la division de a et b, 
                  si ils sont tous les 2 entiers 
                     et que b est différent de 0;
              * Err, sinon 
*) 
let (</>) a b = match (a, b) with
  | Z x, Z y -> if y = 0 then Err else Z (x / y)
  | _ -> Err

(** *****************)
(** **** Question 3 *)
(** *****************)
       
(** eval_arith
    @param : e est une expression arithmétique,
             v est une valuation
    
    @return : l'interprétation de e par la valuation v
*)   
let rec eval_arith (e : 'a exp_arith) (v: 'a valuation) : valeur = match e with
  | Ent n -> Z n
  | Var x -> Z (v x)
  | Plus(e1, e2) ->  (<+>) (eval_arith e1 v) (eval_arith e2 v)
  | Moins(e1, e2) -> (<->) (eval_arith e1 v) (eval_arith e2 v)
  | Fois(e1, e2) ->  (<*>) (eval_arith e1 v) (eval_arith e2 v)
  | Div(e1, e2) ->   (</>) (eval_arith e1 v) (eval_arith e2 v)

(** *****************)
(** **** Question 4 *)
(** *****************)

(** L'expression arithmétique (z + (x-y)) * (x+7) *)
let expression_1 =
  Fois ( Plus ((Var "z"), Moins (Var "x", Var "y")), Plus (Var "x", Ent 7))

(** La valutation {x -> 1, y -> 3, z -> 2} *)
let valuat_1 a = match a with
  |"x" -> 1
  |"y" -> 3
  |"z" -> 2;;

(** L'évaluation de l'expression (z + (x-y)) * (x+7)
    par la valuation {x -> 1, y -> 3, z -> 2} (= Z 0) *)
eval_arith expression_1 valuat_1;;

(** *****************)
(** **** Question 5 *)
(** *****************)

(** L'expression arithmétique (z + (x-y)) / (x-1) *)
let expression_2 =
  Div ( Plus ((Var "z"), Moins (Var "x", Var "y")), Moins (Var "x", Ent 1));;

(** L'évaluation de l'expression (z + (x-y)) / (x-1)
    par la valuation {x -> 1, y -> 3, z -> 2} (= Err) *)
eval_arith expression_2 valuat_1;;

(** ********************************************)
(** *** Sémantique opérationnelle à petits pas *)
(** ********************************************)

(** *****************)
(** **** Question 6 *)
(** *****************)

(** Type des configurations *)
type 'a config = { expr : 'a exp_arith; s : 'a valuation }

(** Exceptions *)
exception Terminale_int of int (* Lorsque l'expression obtenue est terminale *)
exception Erreur               (* Lorsque aucune étape ne peut-être appliquée *)

(** Deux exemples de configurations *)
let config_1 = {expr = expression_1; s = valuat_1}
let config_2 = {expr = expression_2; s = valuat_1}
             
(** etape_sopp_arith
    @param : conf est une configuration

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur conf

    @raise : * Terminale_int v si conf est terminale,
             * Erreur si aucune étape ne peut être appliquée
*)         
let rec etape_sopp_arith conf = match conf.expr with
  | Ent n -> raise (Terminale_int n)
  | Var a -> (* On pourrait supposer que la variable est forcément 
                dans la valuation *)
             (try
               { expr = Ent (conf.s a); s = conf.s}
             with _ -> raise Erreur)
                     
  | Plus(e1, e2) ->
     (match (e1, e2) with
      | (Ent n1, Ent n2) -> { expr = Ent (n1 + n2); s = conf.s }
      | (Ent n1, _) ->
         let res = (etape_sopp_arith ({expr = e2; s = conf.s})) in
         { expr = Plus(Ent n1, res.expr); s = conf.s}
      | _ ->
         let res = etape_sopp_arith ({expr = e1; s = conf.s}) in
         { expr = Plus (res.expr, e2); s = conf.s})
    
  | Moins(e1, e2) ->
     (match (e1, e2) with
      | (Ent n1, Ent n2) -> { expr = Ent (n1 - n2); s = conf.s }
      | (Ent n1, _) ->
         let res = (etape_sopp_arith ({expr = e2; s = conf.s}))
         in { expr = Moins(Ent n1, res.expr); s = conf.s}
      | _ ->
         let res = etape_sopp_arith ({expr = e1; s = conf.s}) in
         { expr = Moins(res.expr, e2); s = conf.s})
    
  | Fois(e1, e2) ->
     (match (e1, e2) with
      | (Ent n1, Ent n2) -> { expr = Ent (n1 * n2); s = conf.s }
      | (Ent n1, _) ->
         let res = (etape_sopp_arith ({expr = e2; s = conf.s})) in
         { expr = Fois(Ent n1, res.expr); s = conf.s}
      | _ ->
         let res = etape_sopp_arith ({expr = e1; s = conf.s}) in
         { expr = Fois(res.expr, e2); s = conf.s})
    
  | Div(e1, e2) ->
     (match (e1, e2) with
      | (Ent n1, Ent n2) ->
         if n2 = 0
         then raise Erreur
         else { expr = Ent (n1 / n2); s = conf.s }
      | (Ent n1, _) ->
         let res = (etape_sopp_arith ({expr = e2; s = conf.s})) in
         { expr = Div(Ent n1, res.expr); s = conf.s}
      | _ ->
         let res = etape_sopp_arith ({expr = e1; s = conf.s}) in
         { expr = Div (res.expr, e2); s = conf.s})
    
(** *****************)                     
(** **** Question 7 *)
(** *****************)
                 
(** eval_sopp_arith
    @param : e est une expression arithmétique,
             v est une valuation

    @return : l'évaluation de e par la valutation v :
                  * Z v si le résultat de l'évaluation est v,
                  * Err sinon
*)               
let rec eval_sopp_arith e (v: 'a valuation) =
  try
    let res = (etape_sopp_arith ({expr = e; s = v})) in
    eval_sopp_arith res.expr res.s
  with  Terminale_int n -> Z n
      | Erreur -> Err;;

(** *****************)
(** **** Question 8 *)
(** *****************)

(** L'évaluation de l'expression (z + (x-y)) * (x+7)
    par la valuation {x -> 1, y -> 3, z -> 2} (= Z 0) *)
eval_sopp_arith expression_1 valuat_1;;

(** L'évaluation de l'expression (z + (x-y)) / (x-1)
    par la valuation {x -> 1, y -> 3, z -> 2} (= Err) *)
eval_sopp_arith expression_2 valuat_1;;

(** ****************************************)
(** ** EXERCICE 2 : Expressions booléennes *)
(** ****************************************)

(** Type des expressions booléennes *)
type 'a exp_bool = Bool of bool
                 | Inf  of 'a exp_arith * 'a exp_arith
                 | Egal of 'a exp_arith * 'a exp_arith
                 | Not  of 'a exp_bool
                 | Or   of 'a exp_bool * 'a exp_bool
                 | And  of 'a exp_bool * 'a exp_bool
                         
(** *************************************************************************)
(** **** Question 0 : Sémantique dénotationnelle des expressions booléennes *)
(** *************************************************************************)
                         
(** Type des valeurs de retour pour les expressions booléennes *)
type valeur_bool = B of bool | Err

(* Note : le type des valuations est le même que précédemment *)
                          
(** _inf_
    @param : a et b sont de type "valeur"
    
    @return : * un "B of bool" correspondant au résultat du test (a<=b), 
                  si ils sont tous les 2 entiers;
              * Err, sinon
*)                         
let _inf_ a b = match (a, b) with
  |Z n1, Z n2 -> B (n1 <= n2)
  | _ -> Err
       
(** _egal_
    @param : a et b sont de type "valeur"
    
    @return : * un "B of bool" correspondant au résultat du test (a=b), 
                  si ils sont tous les 2 entiers;
              * Err, sinon
*)   
let _egal_ a b = match (a, b) with
  |Z n1, Z n2 -> B (n1 = n2)
  | _ -> Err
       
(** _not_
    @param : b est de type "valeur_bool"
    
    @return : * un "B of bool" correspondant à la négation de b,
              * Err, sinon
*)
let _not_ b = match b with
  | B true -> B false
  | B false -> B true
  | _ -> Err
       
(** _or_
    @param : a et b sont de type "valeur_bool"
    
    @return : * un "B of bool" correspondant au résultat de (a or b),
              * Err, sinon
*)
let _or_ a b = match (a, b) with
  |B false, B false -> B false
  |B true, B _ |B false, B true -> B true            
  | _ -> Err
       
(** _and_
    @param : a et b sont de type "valeur_bool"
    
    @return : * un "B of bool" correspondant au résultat de (a and b),
              * Err, sinon
*)
let _and_ a b = match (a, b) with
  |B true,  B true -> B true
  |B false, B _ |B true, B false -> B false             
  | _ -> Err
       
(** eval_bool
    @param : e est une expression booléenne,
             v est une valuation
    
    @return : l'interprétation de e par la valuation v
              (sémantique dénotationnelle)
*)
let rec eval_bool (e : 'a exp_bool) (v: 'a valuation) : valeur_bool =
  match e with
  | Bool b -> B b
  | Inf(e1, e2) ->  _inf_  (eval_arith e1 v) (eval_arith e2 v)
  | Egal(e1, e2) -> _egal_ (eval_arith e1 v) (eval_arith e2 v)
  | Not b ->        _not_  (eval_bool b v)
  | Or(b1, b2) ->   _or_   (eval_bool b1 v) (eval_bool b2 v)
  | And(b1, b2) ->  _and_  (eval_bool b1 v) (eval_bool b2 v)

(** **********************************************************)
(** **** Question 1 : Sémantique opérationnelle à petits pas
                      des expressions booléennes             *)
(** **********************************************************)

(** Type des configurations (booléennes) *)      
type 'a config_bool = { expr_bool : 'a exp_bool; s : 'a valuation }

(** Exception *)
exception Terminale_bool of bool (* Lorsque l'expression obtenue est terminale *)
                          
(* Note : le type des valuations est le même que précédemment *)

(** etape_sopp_bool
    @param : conf est une configuration (booléenne)

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur conf

    @raise : * Terminale_bool v si conf est terminale,
             * Erreur si aucune étape ne peut être appliquée
*)
let rec etape_sopp_bool conf = match conf.expr_bool with
  | Bool b -> raise (Terminale_bool b)           
  | Inf(e1, e2) -> (match (e1, e2) with
                    | (Ent n1, Ent n2) ->
                       { expr_bool = Bool (n1 <= n2); s = conf.s }
                    | _, _ ->
                       let res_e1 = eval_sopp_arith e1 conf.s in
                       let res_e2 = eval_sopp_arith e2 conf.s in
                       if res_e1 = Err || res_e2 = Err then raise Erreur
                       else { expr_bool = Bool (res_e1 <= res_e2); s = conf.s })
                  
  | Egal(e1, e2) -> (match (e1, e2) with
                     | (Ent n1, Ent n2) ->
                        { expr_bool = Bool (n1 = n2); s = conf.s }
                     | _, _ ->
                        let res_e1 = eval_sopp_arith e1 conf.s in
                        let res_e2 = eval_sopp_arith e2 conf.s in
                        if res_e1 = Err || res_e2 = Err then raise Erreur
                        else { expr_bool = Bool (res_e1 = res_e2); s = conf.s })
                  
  | Not b -> (match b with
              | Bool true ->
                 { expr_bool = Bool false ; s = conf.s}
              | Bool false ->
                 { expr_bool = Bool true ; s = conf.s}
              | _ ->
                 let res = etape_sopp_bool ({expr_bool = b; s = conf.s}) in
                 { expr_bool = Not (res.expr_bool); s = conf.s})
           
  | Or (b1, b2) -> (match (b1, b2) with
                    | (Bool false, _) ->
                       { expr_bool = b2 ; s = conf.s }
                    | (Bool true,  _) ->
                       { expr_bool = Bool true ; s = conf.s}
                    | _ ->
                       let res = etape_sopp_bool ({expr_bool = b1; s = conf.s})
                       in { expr_bool = Or (res.expr_bool, b2); s = conf.s})
                  
  | And(b1, b2) -> (match (b1, b2) with
                    | (Bool true,  _) ->
                       { expr_bool = b2 ; s = conf.s }
                    | (Bool false, _) ->
                       { expr_bool = Bool false; s = conf.s}
                    | _ ->
                       let res = etape_sopp_bool ({expr_bool = b1; s = conf.s})
                       in { expr_bool = And (res.expr_bool, b2); s = conf.s})

(** eval_sopp_bool
    @param : e est une expression booléenne,
             v est une valuation

    @return : l'évaluation de e par la valutation v :
                  * B b si le résultat de l'évaluation est b,
                  * Err sinon
*)        
let rec eval_sopp_bool e (v: 'a valuation) =
  try
    let res = etape_sopp_bool ({expr_bool = e; s = v}) in
    eval_sopp_bool res.expr_bool res.s
  with  Terminale_bool b -> B b
      | Erreur -> Err;;

(** *************************************************)
(** **** Question 2 : Comparaison des 2 sémantiques *)
(** *************************************************)

(** L'expression booléenne not( x=0 and (x<=(7/z) ) *)
let expression_bool =
  Not (And(Egal(Var "x", Ent 0), Inf(Var "x", Div(Ent 7, Var "z"))));;

(** La valutation {x -> 0, z -> 0} *)
let valuat_2 a = match a with
  |"x" -> 0
  |"z" -> 0;;

(** Sémantique dénotationnelle des expressions booléennes *)
eval_bool expression_bool valuat_1;; (* donne B true *)
eval_bool expression_bool valuat_2;; (* donne Err *)

(** Sémantique opérationnelle à petit pas des expressions booléennes *)
eval_sopp_bool expression_bool valuat_1;; (* donne B true *)
eval_sopp_bool expression_bool valuat_2;; (* donne Err *)

(** Tests additionnels *)

(** L'expression booléenne not( x=0 or (x<=(7/z) ) *)
let expression_bool_2 =
  Not (Or(Egal(Var "x", Ent 0), Inf(Var "x", Div(Ent 7, Var "z"))));;

(** Sémantique dénotationnelle des expressions booléennes *)
eval_bool expression_bool_2 valuat_1;; (* donne B false *)
eval_bool expression_bool_2 valuat_2;; (* donne Err *)

(** Sémantique opérationnelle à petit pas des expressions booléennes *)
eval_sopp_bool expression_bool_2 valuat_1;; (* donne B false *)
eval_sopp_bool expression_bool_2 valuat_2;; (* donne B false *)

(** *********************)
(** ** EXERCICE 3 : IMP *)
(** *********************)

(** Type des valuations *)
module SM = Map.Make(String)
type valu = int SM.t

(** valuation_of_valu
    @param : 's' est une valuation de type valu

    @return : retourne la valuation correspondante de type 'string valuation'
*) 
let valuation_of_valu (s : valu) : string valuation = fun x -> SM.find x s

(** *****************)
(** **** Question 1 *)
(** *****************)

(** affiche_variable
    @param : variable est de type string,
             value est de type int

    @return : Affiche "variable -> value"
*) 
let affiche_variable variable value =
  print_string(variable);
  print_string(" -> ");
  print_string(string_of_int value);
  print_string("\n")
  
(** affiche_valu
    @param : v est une valuation

    @return : Affiche la valuation v
*)                                             
let affiche_valu v =
  print_string("{");
  SM.iter affiche_variable v;
  print_string("}\n");;
(* Note :   iter : (key -> 'a -> unit) -> 'a t -> unit *)

(** La valutation {x -> 2, y -> 3, z -> 4} *)
let valuat_3 = SM.add "x" 2 (SM.add "y" 3 (SM.add "z" 4 SM.empty));;

(** Exemple d'affichage *)
affiche_valu valuat_3;;
                                                     
(** *****************)
(** **** Question 2 *)
(** *****************)

(** Type des programmes IMP *)
type imp =
  Skip
| Aff   of string * string exp_arith
| Seq   of imp * imp
| If    of string exp_bool * imp * imp
| While of string exp_bool * imp
         
(** Type des configurations IMP *)      
type config_imp = { prgm_imp : imp; s : valu }

(** Exception *)
exception Terminale_imp of imp (* Lorsque l'expression obtenue est terminale *)

(** etape_sopp_imp
    @param : conf est une configuration IMP

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur conf

    @raise : * Terminale_imp Skip si conf est terminale,
             * Erreur si une expression booléenne ou arithmétique
                         ne peut pas être évaluée
*)
let rec etape_sopp_imp conf = match conf.prgm_imp with
  | Skip -> raise (Terminale_imp Skip)           
  | Aff(x, e) -> let v = valuation_of_valu conf.s in
                 (match (eval_sopp_arith e v) with
                  | Err -> raise Erreur
                  | Z n -> { prgm_imp = Skip ; s = SM.add x n (conf.s) })
                 
  | Seq(p1, p2) ->
     (match p1 with
      | Skip -> { prgm_imp = p2 ; s = conf.s }
      | _ -> let res = etape_sopp_imp ({ prgm_imp = p1 ; s = conf.s}) in
             { prgm_imp = Seq(res.prgm_imp, p2) ; s = res.s})
    
  | If(eb, p1, p2) -> let v = valuation_of_valu conf.s in
                      (match (eval_sopp_bool eb v) with
                       | B true ->
                          { prgm_imp = p1 ; s = conf.s}
                       | B false ->
                          { prgm_imp = p2 ; s = conf.s}
                       | Err -> raise Erreur)
                      
  | While(eb, p) as curr_pgrm -> let v = valuation_of_valu conf.s in
                                 (match (eval_sopp_bool eb v) with
                                  | B true ->
                                     { prgm_imp = Seq(p, curr_pgrm) ; s = conf.s}
                                  | B false ->
                                     { prgm_imp = Skip ; s = conf.s}
                                  | Err -> raise Erreur)
                                 

(** eval_sopp_imp
    @param : p est un programme,
             v est une valuation (de type valu)

    @return : la valuation après exécution du programme p

    @raise : "Erreur" quand il n'est pas possible d'évaluer 
             une expression booléenne ou arithmétique
*)        
let rec eval_sopp_imp p (v: valu) =
  try
    let res = etape_sopp_imp ({prgm_imp = p; s = v}) in
    eval_sopp_imp res.prgm_imp res.s
  with  Terminale_imp _ -> v
      | Erreur -> raise Erreur;;

(** *****************)
(** **** Question 4 *)
(** *****************)

(** Le programme : x := 24; y := 36; while not(x=y) do if x<=y then y:=y-x 
                                                       else x:=x-y         *)
let prog = Seq (Aff("x", Ent 24),
                Seq (Aff("y", Ent 36),
                     While(Not(Egal(Var "x", Var "y")),
                           If( Inf( Var "x", Var "y"),
                               Aff("y", Moins(Var "y", Var "x")),
                               Aff("x", Moins(Var "x", Var "y"))
                             )
                       )
                  )
             );;

(** L'évaluation du programme précédent par la valuation vide.
    Le résultat est la valuation {x -> 12, y -> 12}            *)
let res = eval_sopp_imp prog (SM.empty);;
affiche_valu res;;

(** ***************************)
(** ** EXERCICE 4 : MiniML    *)
(** ***************************)

(** ***********************************)
(** ***  PARTIE A : Encodage profond  *)
(** ***********************************)

(** Type des expressions fonctionnelles de MiniML *)
type miniml =
  Const of int
| Var   of string
| Fun   of string * miniml
| App   of miniml * miniml
| Plus  of miniml * miniml

(** fresh_var
    @return : Retourne un nom de variable frais
*)       
let fresh_var =
  let counter = ref 0 in
  fun() -> incr  counter; Printf.sprintf "x%i" !counter;;

(** Un exemple de variable fraiche *)
fresh_var () ;;

(** *****************)
(** **** Question 1 *)
(** *****************)

(** subst
    @param : x est une variable (de type string),
             t et s sont des expressions fonctionnelles de MiniML

    @return : l'expression fonctionnelle où la variable x
              a été substituée par t dans s
*)  
let rec subst x t s = match s with
  | Const a -> Const a
  | Var y -> if x = y then t else s
  | Fun(y, e) -> let z = fresh_var () in
                 Fun(z, (subst x t (subst y (Var z) e)))
  | App (e1, e2) ->  App((subst x t e1), (subst x t e2))
  | Plus(e1, e2) -> Plus((subst x t e1), (subst x t e2))

(** *****************)
(** **** Question 2 *)
(** *****************)
                  
(** Type des valeurs de retour pour les expressions fonctionnelles *)
type valeur_fonc = Z of int | Abs of string * miniml
                                
(** Exception *)
exception Terminale_fonc of valeur_fonc (* Lorsque l'expression obtenue 
                                           est terminale *)

(** ss_val_step
    @param : expr_fonc est une expression fonctionnelle

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur expr_fonc

    @raise : * Terminale_fonc _ si expr_fonc est terminale,
             * Erreur si une nous obtenons une variable (libre)
*)
let rec ss_val_step expr_fonc = match expr_fonc with
  | Const a -> raise (Terminale_fonc (Z a))
  | Var x -> raise Erreur    
  | Fun(x, ef) -> raise (Terminale_fonc (Abs(x, ef)))
                  
  | App(ef1, ef2) -> (match (ef1, ef2) with
                      | Fun(x, e), Const a   -> subst x ef2 e
                      | Fun(x, e), Fun(_, _) -> subst x ef2 e 
                      | Fun(x, e), _ -> let res = ss_val_step ef2 in
                                        App(ef1, res)
                      | _ -> App(ss_val_step ef1, ef2))

  | Plus(ef1, ef2) -> (match (ef1, ef2) with
                      | Const a, Const b -> Const (a + b)
                      | Const a, _ -> let res = ss_val_step ef2 in
                                        Plus(ef1, res)
                      | _ -> Plus(ss_val_step ef1, ef2))

(** *****************)
(** **** Question 3 *)
(** *****************)
                    
(** ss_val
    @param : expr_fonc est une expression fonctionnelle

    @return : la valeur (entier ou abstraction) de l'expression fonctionnelle

    @raise : Erreur si nous obtenons une variable (libre)
*)        
let rec ss_val expr_fonc =
  try
    let res = ss_val_step expr_fonc in
    ss_val res
  with  Terminale_fonc (Z a) -> Z a
      | Terminale_fonc (Abs(x, ef)) -> (Abs(x, ef))
      | Erreur -> raise Erreur;;

(** *****************)
(** **** Question 4 *)
(** *****************)

(** L'expression fonctionnelle 
         ( (fun x -> (fun y -> x+y)) 1 ) ( ((fun x -> 3) 1) + 2 ) *)
let efm1 = App( App
                  (Fun("x", ( Fun("y", (Plus(Var "x", Var "y")) ) ) ),
                   (Const 1) ),
                (Plus
                   (App( Fun("x", (Const 3)), (Const 1) ),
                    (Const 2) ) ) );;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est Z 6.  *)
ss_val efm1;;

(** *****************)
(** **** Question 5 *)
(** *****************)

(** ss_nom_step
    @param : expr_fonc est une expression fonctionnelle

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur expr_fonc

    @raise : * Terminale_fonc _ si expr_fonc est terminale,
             * Erreur si nous obtenons une variable (libre)
*)
let rec ss_nom_step expr_fonc = match expr_fonc with
  | Const a -> raise (Terminale_fonc (Z a))
  | Var x -> raise Erreur    
  | Fun(x, ef) -> raise (Terminale_fonc (Abs(x, ef)))
                  
  | App(ef1, ef2) -> (match (ef1, ef2) with
                      | Fun(x, e), _ -> subst x ef2 e
                      | _ -> App(ss_nom_step ef1, ef2))

  | Plus(ef1, ef2) -> (match (ef1, ef2) with
                      | Const a, Const b -> Const (a + b)
                      | Const a, _ -> let res = ss_nom_step ef2 in
                                        Plus(ef1, res)
                      | _ -> Plus(ss_nom_step ef1, ef2))
                    
(** ss_nom
    @param : expr_fonc est une expression fonctionnelle

    @return : la valeur (entier ou abstraction) de l'expression fonctionnelle

    @raise : Erreur si nous obtenons une variable (libre)
*)      
let rec ss_nom expr_fonc =
  try
    let res = ss_nom_step expr_fonc in
    ss_nom res
  with  Terminale_fonc (Z a) -> Z a
      | Terminale_fonc (Abs(x, ef)) -> (Abs(x, ef))
      | Erreur -> raise Erreur;;

(** *****************)
(** **** Question 6 *)
(** *****************)

(** L'expression fonctionnelle (fun x -> x x) *)
let delta = Fun("x", (App(Var "x", Var "x")));;

(** L'expression fonctionnelle (fun x -> 1) (delta delta) *)
let efm2 = App( (Fun("x", (Const 1))), (App(delta, delta)) );;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est "Stack overflow during evaluation (looping recursion?)"  *)
ss_val efm2;;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est Z 1.  *)
ss_nom efm2;;

(** ******************************************************)
(** ***  PARTIE B : Syntaxe abstraite d'ordre supérieur  *)
(** ******************************************************)

(** Type des expressions fonctionnelles de MiniML (Syntaxe abstraite) *)
type miniml_abstrait =
  Const_abstrait of int
| Var_abstrait   of string
| Fun_abstrait   of (miniml_abstrait -> miniml_abstrait)
| App_abstrait   of miniml_abstrait * miniml_abstrait
| Plus_abstrait  of miniml_abstrait * miniml_abstrait

(** *****************)
(** **** Question 2 *)
(** *****************)
        
(** Type des valeurs de retour pour les expressions fonctionnelles 
    (Syntaxe abstraite) *)
type valeur_fonc_abstrait = Z_abstrait of int
                          | Abs_abstrait of (miniml_abstrait -> miniml_abstrait)
                                
(** Exception *)
exception Terminale_fonc_abstrait of valeur_fonc_abstrait
(* Lorsque l'expression obtenue est terminale *)
                                   
(** ss_val_step_abstrait
    @param : expr_fonc est une expression fonctionnelle

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur expr_fonc

    @raise : * Terminale_fonc _ si expr_fonc est terminale,
             * Erreur si une nous obtenons une variable (libre)
*)
let rec ss_val_step_abstrait (expr_fonc : miniml_abstrait) =
  match expr_fonc with
  | Const_abstrait a -> raise (Terminale_fonc_abstrait (Z_abstrait a))
  | Var_abstrait x ->   raise Erreur    
  | Fun_abstrait f ->   raise (Terminale_fonc_abstrait (Abs_abstrait f))
                     
  | App_abstrait(ef1, ef2) ->
     (match (ef1, ef2) with
      | Fun_abstrait f, Const_abstrait a -> f ef2
      | Fun_abstrait f, Fun_abstrait _ -> f ef2  
      | Fun_abstrait f, _ -> let res = ss_val_step_abstrait ef2 in
                             App_abstrait(ef1, res)
      | _ -> App_abstrait(ss_val_step_abstrait ef1, ef2))
    
  | Plus_abstrait(ef1, ef2) ->
     (match (ef1, ef2) with
      | Const_abstrait a, Const_abstrait b -> Const_abstrait (a + b)
      | Const_abstrait a, _ -> let res = ss_val_step_abstrait ef2 in
                               Plus_abstrait(ef1, res)
      | _ -> Plus_abstrait(ss_val_step_abstrait ef1, ef2))
                             
(** *****************)
(** **** Question 3 *)
(** *****************)
                    
(** ss_val_abstrait
    @param : expr_fonc est une expression fonctionnelle

    @return : la valeur (entier ou abstraction) de l'expression fonctionnelle

    @raise : Erreur si nous obtenons une variable (libre)
*)        
let rec ss_val_abstrait expr_fonc =
  try
    let res = ss_val_step_abstrait expr_fonc in
    ss_val_abstrait res
  with  Terminale_fonc_abstrait (Z_abstrait a) -> Z_abstrait a
      | Terminale_fonc_abstrait (Abs_abstrait f) -> Abs_abstrait f
      | Erreur -> raise Erreur;;

(** *****************)
(** **** Question 4 *)
(** *****************)

(** L'expression fonctionnelle 
        ( (fun x -> (fun y -> x+y)) 1 ) ( ((fun x -> 3) 1) + 2 ) *)
let efm1_abstrait =
  App_abstrait( App_abstrait
                  (Fun_abstrait(fun x -> ( Fun_abstrait(fun y ->
                                               (Plus_abstrait(x, y)) ) ) ),
                   (Const_abstrait 1) ),
                (Plus_abstrait
                   (App_abstrait( Fun_abstrait(fun x ->
                                      (Const_abstrait 3)), (Const_abstrait 1) ),
                    (Const_abstrait 2) ) ) );;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est Z_abstrait 6 *)
ss_val_abstrait efm1_abstrait;;

(** *****************)
(** **** Question 5 *)
(** *****************)

(** ss_nom_step_abstrait
    @param : expr_fonc est une expression fonctionnelle

    @return : une configuration résultante après application d'une étape 
              de la sémantique opérationnelle à petit pas sur expr_fonc

    @raise : * Terminale_fonc _ si expr_fonc est terminale,
             * Erreur si nous obtenons une variable (libre)
*)
let rec ss_nom_step_abstrait expr_fonc = match expr_fonc with
  | Const_abstrait a -> raise (Terminale_fonc_abstrait (Z_abstrait a))
  | Var_abstrait x ->   raise Erreur    
  | Fun_abstrait(f) ->  raise (Terminale_fonc_abstrait (Abs_abstrait f))
                     
  | App_abstrait(ef1, ef2) ->
     (match (ef1, ef2) with
      | Fun_abstrait(f), _ -> f ef2
      | _ -> App_abstrait(ss_nom_step_abstrait ef1, ef2))
    
  | Plus_abstrait(ef1, ef2) ->
     (match (ef1, ef2) with
      | Const_abstrait a, Const_abstrait b -> Const_abstrait (a + b)
      | Const_abstrait a, _ -> let res = ss_nom_step_abstrait ef2 in
                               Plus_abstrait(ef1, res)
      | _ -> Plus_abstrait(ss_nom_step_abstrait ef1, ef2))
                             
(** ss_nom_abstrait
    @param : expr_fonc est une expression fonctionnelle

    @return : la valeur (entier ou abstraction) de l'expression fonctionnelle

    @raise : Erreur si nous obtenons une variable (libre)
*)      
let rec ss_nom_abstrait expr_fonc =
  try
    let res = ss_nom_step_abstrait expr_fonc in
    ss_nom_abstrait res
  with  Terminale_fonc_abstrait (Z_abstrait a) -> Z_abstrait a
      | Terminale_fonc_abstrait (Abs_abstrait f) -> (Abs_abstrait f)
      | Erreur -> raise Erreur;;

(** *****************)
(** **** Question 6 *)
(** *****************)

(** L'expression fonctionnelle (fun x -> x x) *)
let delta_abstrait = Fun_abstrait(fun x -> (App_abstrait (x, x)));;

(** L'expression fonctionnelle (fun x -> 1) (delta delta) *)
let efm2_abstrait = App_abstrait(
                        (Fun_abstrait(fun x -> (Const_abstrait 1))),
                        (App_abstrait(delta_abstrait, delta_abstrait)) );;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est "Stack overflow during evaluation (looping recursion?)" *)
ss_val_abstrait efm2_abstrait;;

(** L'évalutation de l'expression fonctionnelle précédente.
    Le résultat est Z_abstrait 1 *)
ss_nom_abstrait efm2_abstrait;;
