type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
  Letrec of ide * exp * exp
	(* implementazione dizionario e varie operazioni *)
	| Estring of string
	| Read of ide * exp (* chiave da cercare nel dizionario *)
	| Add of ide * exp * exp (* chiave da aggiungere nel dizionario (crea un nuovo dict) *)
	| Remove of ide * exp (* chiave da eliminare dal dizionario *)
	| Clear of exp (* svuota dict *)
	| ApplyOver of exp * exp
	| IsEquals of exp * exp (* controlla se due dizionari contengono gli stessi elementi *) 
  | Dict of dict 
  and dict = Empty | Item of ide * exp * dict;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun  
(* implementazione *) 
| String of string
| Exception of string
| DictVal of evDict
and evDict = (ide * evT) list 
(* *)
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	"string" -> (match v with
		String(_)-> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

let rec isIn (key : ide) (lis : evDict) : bool =
	match lis with 
		[] -> false
	| (i, el)::els -> if i = key then true else isIn key els;;

let rec areIn (key : ide) (v : evT) (lis : evDict) : bool =
	match lis with 
		[] -> false
	| (i, el)::els -> if (i = key && v = el) then true else areIn key v els;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
								_ -> failwith("non functional def")) |

	(* implementazione *)
	Dict(d) -> 
		let rec evalList (dlist : dict) : evDict = 
			(match dlist with
				Empty -> []
			|	Item(key, value, ds) -> 
					let evalue = eval value r in
					(key, evalue)::evalList ds)
		in DictVal(evalList d) |

	(* restituisce l'elemento di chiave key *)
	Read(key, d) ->
		(match eval d r with
			DictVal dvlist -> 
			let rec find (k : ide) (dlist : evDict) : evT = 
				(match dlist with 
					[] -> Exception("not in")
				|	(i, v)::xs -> if (i = k) then v 
												else find k xs)
			in find key dvlist
		|	_ -> Exception("not a dict")) |

	(* aggiunge l'elemento di chiave key, se key non è già nel dizionario*)
	Add(key, value, d) -> 
		(match eval d r with
			DictVal dvlist -> 
				let evalue = eval value r in
				if (not(isIn key dvlist)) then DictVal((key, evalue)::dvlist)
				else Exception("already in")
			| _ -> Exception("not a dict")) |
			
	(* rimuove l'elemento assocciato alla chiave *)
	Remove(key, d) -> 
		(match eval d r with
			DictVal dvlist -> 
				if (isIn key dvlist) then
					let rec rm (k : ide) (dlist : evDict) : evDict = 
						(match dlist with 
							[] -> []
						|	(i, v)::xs -> if (i = k) then xs
														else  (i, v)::(rm k xs))
					in DictVal(rm key dvlist)
				else Exception("key not in")
			| _ -> Exception("not a dictionary")) |

	(* svuota il dizionario *)
	Clear(d) ->
		(match eval d r with
			DictVal dvlist -> DictVal([])
		| _ -> Exception("not a dictionary")) |

	(* applicazione di funzioni con parametri interi *)
	ApplyOver(f, dict) -> 
		(match (f, dict) with
			(Fun(arg, fBody), Dict dv) -> 
        let rec apply (fn : (ide * exp)) (dlist : dict) : evDict  =
					(match dlist with
						Empty -> [] 
          | Item (i, v, xs) -> if (typecheck "int" (eval v r)) then (i, (eval (FunCall(f, v)) r))::apply fn xs
          										 else (i, (eval v) r)::apply fn xs) 
				in DictVal(apply (arg, fBody) dv)
			| _, _ -> Exception("type error")) |

	(* controlla se due dizionari contengono gli stessi elementi *)
	IsEquals(d1, d2) -> 
		(match (eval d1 r, eval d2 r) with 
			(DictVal d_1, DictVal d_2) ->
				if (List.length d_1 = 0 && List.length d_2 = 0) then Bool true
				else let rec member (dict1 : evDict) (dict2 : evDict) : evT =
					 match dict1 with
						[] -> Bool true 
					| (i1, v1)::xs -> if (areIn i1 v1 dict2) then member xs dict2 
																		 else Bool false
				in member d_1 d_2 
			| _, _ -> Exception("type error"))
;;
				
(* TESTS *)

let env0 = emptyenv Unbound;;

let mydict = Dict(Item("nome", Estring("federico"), Item("eta'", Eint 22, Empty)));;

let mydict1 = Dict(Item("nome", Estring("giovanni"), Item("annoNascita", Eint 1990, Empty)));;

let mydict2 = Add("matricola", Eint 536683, mydict);;
let mydict3 = Add("eta'", Eint 24,  mydict);;
let mydict4 = Add("eta'", Eint 24,  mydict1);;

let mydict5 = Remove("matricola", mydict);;
let mydict6 = Remove("eta'", mydict);;
let mydict7 = Remove("matricola", mydict1);;

let mydict8 = Clear(mydict);;

let f = Fun("y", Sum(Den "y", Eint 1));;

print_string("\n\n\n--------------eseguo--------------\n\n\n");;

print_string("creo dizionari con elementi");;
eval mydict env0;;
eval mydict1 env0;;

print_string("\n\nleggo valore 'eta'' dal dizionario 'mydict'");;
eval mydict env0;;
eval (Read("eta'", mydict)) env0;;

print_string("\n\nleggo valore 'eta'' e 'nome' dal dizionario 'mydict1'");;
eval mydict1 env0;;
eval (Read("eta'", mydict1)) env0;;
eval (Read("nome", mydict1)) env0;;

print_string("\n\naggiungo valore <matricola, 536683> al dizionario dict");;
eval mydict env0;;
eval mydict2 env0;;
print_string("\naggiungo valore <eta, 24> al dizionario dict");;
eval mydict3 env0;;

print_string("\n\naggiungo valore <eta, 24> al dizionario dict1");;
eval mydict1 env0;;
eval mydict4 env0;;

print_string("\n\nrimuovo valore 'eta' dal dizionario dict");;
eval mydict env0;;
eval mydict6 env0;;

print_string("\n\nrimuovo valore 'matricola' dal dizionario dict1");;
eval mydict1 env0;;
eval mydict7 env0;; 

print_string("\n\nsvuoto dizionario dict");;
eval mydict env0;;
eval mydict8 env0;;

print_string("\n\napplico funzione f(x) = x + 1 agli elementi dei dizionari interi creando nuovi dizionari");;
eval mydict env0;;
eval (ApplyOver(f, mydict)) env0;;
print_newline();;
eval mydict1 env0;;
eval (ApplyOver(f, mydict1)) env0;;

print_string("\n\ncontrollo se due dizionari contengono gli stessi elementi");;
print_string("mydict = mydict1: ");;
eval(IsEquals (mydict, mydict1))env0;;
print_string("mydict = mydict: ");;
eval(IsEquals (mydict, mydict))env0;;
print_newline();;
