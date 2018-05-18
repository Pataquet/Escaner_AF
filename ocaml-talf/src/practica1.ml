#load "talf.cma";;
open Conj;; (*operaciones con conjuntos*)
open Auto;; (*estructuras algebraicas*)
open Ergo;; (*manejo de la sintaxis*)
open Graf;;

let a1 = af_of_file "/home/mario/Dropbox/TC/Practica 1/automatas/ejer2.comparacion5.txt";;
let a2 = af_of_file "/home/mario/Dropbox/TC/Practica 1/automatas/ejer2.comparacion6.txt";;
let a3 = af_of_file "/home/mario/Dropbox/TC/Practica 1/automatas/ejer2.comparacion7.txt";;

let es_afne = function 
	Af(Conjunto(lEstados), Conjunto(lTerminales), _,
		Conjunto(lArcos), Conjunto(lEstadosFinales)) ->
		let rec aux lArcos = 
			match lArcos with
			| [] -> false
			| Arco_af (e1,e2,(Terminal ""))::t -> true
			| Arco_af (e1,e2,terminal)::t -> aux t
		in aux lArcos;;

let rec es_afn = function
	Af(Conjunto(lEstados), Conjunto(lTerminales), _,
		Conjunto(lArcos), Conjunto(lEstadosFinales)) ->
			let rec aux lArcos conjuntoArcos =
				match lArcos with
				| [] -> false
				| Arco_af (e1,e2,terminal)::t ->
					let cardAntes = cardinal conjuntoArcos in 
					let conjArcosActualizado = agregar (Arco_af (e1,e2,(Terminal ""))) conjuntoArcos in
					if cardAntes == (cardinal conjArcosActualizado) then 
						true
					else 
						aux t conjArcosActualizado
			in aux lArcos (Conjunto []);;


(*Otra opcion de la de justo encima, la que me dijo tou*)
(*let rec es_afn = function
	Af(Conjunto(lEstados), Conjunto(lTerminales), _,
		Conjunto(lArcos), Conjunto(lEstadosFinales)) ->
			let rec aux lArcos conjuntoArcos =
				match lArcos with
				| [] -> false
				| Arco_af (e1,e2,terminal)::t ->
					match 
						 (cardinal conjuntoArcos),
						 (agregar (Arco_af (e1,e2,(Terminal ""))) conjuntoArcos)
					with 
						cardinalAntes, conjActualizado->
						if cardinalAntes == (cardinal conjActualizado) then 
							true
						else 
							aux t conjActualizado
			in aux lArcos (Conjunto []);; *)


let es_afd automata = (not (es_afn automata)) && ( not (es_afne automata));;


(*Ejercicio 2*)


let rec repetidos lhijos lvisitados lNoVisitados= 
	match lhijos with
		| Conjunto [] -> lNoVisitados
		| Conjunto (h::t) ->
			if (pertenece h lvisitados) then 
				repetidos (Conjunto t) lvisitados lNoVisitados
			else 
				repetidos (Conjunto t) lvisitados (agregar h lNoVisitados);;


let rec comprobarTerminal estadoactual term lArcos lhijos  = 
	match lArcos with
		| [] -> []
		| Arco_af (e1,e2,terminal)::t ->
			if (e1 = estadoactual) && (terminal=term) then (e2::lhijos)
			else comprobarTerminal estadoactual term t lhijos;;

let mismoEstado estado1 estado2 estadosFinales1 estadosFinales2=
	match estado1,estado2 with
	| (h1::t1, h2::t2)-> 
		((pertenece h1 estadosFinales1) && (pertenece h2 estadosFinales2))
		|| (not(pertenece h1 estadosFinales1) && not(pertenece h2 estadosFinales2));;

let add e1 e2 lestados =
	match e1,e2 with
	| (h1::t1, h2::t2)-> (agregar (h1,h2) lestados);;


let rec hijos lTerminales (p1,p2) (arco1,arco2) estadosFinales1 estadosFinales2 lVisitados lsolucion=
	match lTerminales with
	| [] -> repetidos lsolucion lVisitados (Conjunto [])
	| h::t ->
		match (comprobarTerminal p1 h arco1 []),(comprobarTerminal p2 h arco2 []) with
		| ([],[]) -> hijos t (p1,p2) (arco1,arco2) estadosFinales1 estadosFinales2 lVisitados lsolucion
		| ([],e2) -> 
			Printf.printf "1 Lista vacia";
			raise Not_found
		| (e1,[]) ->
			Printf.printf "2 Lista vacia";
			raise Not_found
		| (e1,e2) -> if mismoEstado e1 e2 estadosFinales1 estadosFinales2 then
						hijos t (p1,p2) (arco1,arco2) estadosFinales1 estadosFinales2 lVisitados (add e1 e2 lsolucion)
					else(
						Printf.printf "Estados diferentes ";
						raise Not_found);;


let equivalentes automata1 automata2 =
	match automata1, automata2 with
		| (Af(Conjunto(lEstados1), Conjunto(lTerminales1), estadoactual1,Conjunto(lArcos1), lEstadosFinales1)),
		  (Af(Conjunto(lEstados2), Conjunto(lTerminales2), estadoactual2,Conjunto(lArcos2), lEstadosFinales2)) -> 
  	if igual (Conjunto lTerminales1) (Conjunto lTerminales2) then
	(	  	
		let rec aux lpendientes lVisitados = 
	  		match lpendientes with
	  		| Conjunto [] -> true
	  		| Conjunto (h::t) ->
	  			try 
	  				match (hijos lTerminales1 h (lArcos1,lArcos2) lEstadosFinales1 lEstadosFinales2 lVisitados (Conjunto [])) with
	  				| c -> aux (union (Conjunto t) c) (union lVisitados c)
	  			with
					Not_found -> false

		in aux (Conjunto([estadoactual1,estadoactual2])) (Conjunto([estadoactual1,estadoactual2]))
	)
	else(
		Printf.printf "Lenguages diferentes ";
		false );;





(*Ejercicio 3 a*)

let rec comprobarTerminales estadoactual term lArcos lhijos  = 
	match lArcos with
		| [] -> lhijos
		| Arco_af (e1,e2,terminal)::t ->
			if (e1 = estadoactual) && (terminal=term) then(
				comprobarTerminales estadoactual term t (e2::lhijos))
			else comprobarTerminales estadoactual term t lhijos;;


let rec comprobarFin lhijos finales = 
	match lhijos with
	| Conjunto [] -> false
	| Conjunto (h::t) -> if pertenece h finales then true 
			else comprobarFin (Conjunto t) finales;;

let escaner_afn cadena automata = 
	match automata with
		| (Af(Conjunto(lEstados), Conjunto(lTerminales),
			estadoactual,Conjunto(lArcos), estadosFinales)) -> 
	let rec aux cadena lhijos= 
		match cadena with
		| [] -> comprobarFin lhijos estadosFinales
		| h::t ->
			match lhijos with
			| Conjunto [] -> false
			| Conjunto (h2::t2) ->
				aux t (union (Conjunto t2)
					(Conjunto(comprobarTerminales h2 h lArcos [])))
	in aux cadena (Conjunto [estadoactual]);;

(*Ejercicio 3 b*)
	
let rec comprobarTerminales2 estadoactual term lArcos  = 
	match lArcos with
		| [] -> []
		| Arco_af (e1,e2,terminal)::t ->
			if (e1 = estadoactual) && (terminal=term) then
				[e2]
			else comprobarTerminales2 estadoactual term t;;


let escaner_afd cadena automata = 
	match automata with
		| (Af(Conjunto(lEstados), Conjunto(lTerminales),
			estadoactual,Conjunto(lArcos), estadosFinales)) -> 
	let rec aux cadena estado= 
		match cadena with
		| [] -> (comprobarFin (Conjunto estado) estadosFinales)
		| h::t ->match estado with
			| [] -> false
			| h2::t2 -> aux t (comprobarTerminales2 h2 h lArcos)
	in aux cadena [estadoactual];;