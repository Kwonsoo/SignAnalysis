(*===========================
	language(program) definition
=============================*)
type id = String.t

type exp = 
	| NUM of int
	| VAR of id
	| ADD of exp * exp
	| EQUAL of exp * exp
	| LESS of exp * exp
	| NOT of exp

type stmt =
	| READ of id
	| WRITE of exp
	| ASSIGN of id * exp
	| IF of exp * stmt * stmt
	| WHILE of exp * stmt
	| SEQ of stmt * stmt

type pgm = stmt

(*==================================================================================== 
	여기 정의되어있는 것들은 language 정의와 관련 없다.
	몇 가지 작은 프로그램들에 이름을 붙여놓고 분석을 진행할 때 사용하고 싶은 것 뿐이다.
	그냥 위의 language syntax에 따라 만들어본 간단한 테스트 프로그램들이 되겠지.
 =====================================================================================*)
(* read x *)
let inputx = READ "x"
(* x := x + 1 *)
let incx = ASSIGN ("x", ADD (VAR "x", NUM 1))
(* x := 0 *)
let p0 = ASSIGN ("x", NUM 0)
(* x := 1 *)
let p1 = ASSIGN ("x", NUM 1)
(* y := -1 *)
let p2 = ASSIGN ("y", NUM (-1))
(* x := 1; y := -1 *)
let p3 = SEQ (p1, p2)
(* 
	while (1)
		x := x + y
*)
let p4 = WHILE (NUM 1, ASSIGN ("x", ADD (VAR "x", VAR "y")))
(*
	x := 1;
	y := -1;
	while (1)
		x := x + y
*)
let p5 = SEQ (p3, p4)
(* if (1) p0 p1 *)
let p6 = IF (NUM 1, p0, p1)
(*
	read x;
	while (x < 10)
		x := x + 1
*)
let p7 = SEQ (inputx, WHILE (LESS (VAR "x", NUM 10), incx))
let p = p5

(*==================================================================================================================
	위에 program definition 부분에서 우리가 분석하려는 분석 대상 language의 구성 요소들의 syntax를 정의했다.
	분석 대상 language는 외부에서 우리에게 주어진 것이다. 당연히 syntax 뿐만 아니라 semantics도 정의되어 있다.
	그런데 이 semantics (concrete semantics)는 language를 만들 때 정의된 것이고 우리의 관심사는 아니다.
	
	우리의 관심사는 해당 language에 대해 abstract semantics를 정의하고 그에 따라 분석을 진행하고 싶은 것이다.
	진행할 분석의 종류도 우리가 선택한다. 이번에는 Sign Analysis.
	우리가 하려는 분석에 맞게 semantics를 정의해주면 되는 것이다.
 
	이제부터 우리가 하려는 분석에 맞게 (abstract semantic domain을 포함한)	abstract semantics를 정의한다.
	즉, (concrete이 아닌) abstract한 세계에서 semantic domain을 정의하고 최종 semantics 정의를 완성하려고 하는 것이다.
	이게 완성되면 이에 따라 분석을 실행시키면 그만이다.

	여기 정의하는 모든 모듈은 이론적으로 CPO가 되겠지 (되어야 하겠지).
	CPO는 order도 가지고 있고 lub도 있고 ...
	--------------------------------------------------------------------------
	
	[ interval domain으로 확장할 때 ]
	Sign 도멘인 대신 interval 도메인 구현하면 되고,
	widen, narrow 구현해줘서 적용해주면 됨. (fixpoint 구할 때 적용해주는 것.)
===================================================================================================================*)


(*====================================================
	abstract domain: Sign (CPO)
======================================================*)
module Sign = struct
	type t = Bot | Top | Minus | Plus | Zero

	let bot = Bot
	let top = Top

	(* abstraction function (Galois Connection) *)
	let alpha: int -> t
	= fun n ->
		if n > 0 then Plus
		else if n < 0 then Minus
		else Zero
	
	(* order (CPO): true iff x |= y *)
	let order: t -> t -> bool
	= fun s1 s2 ->
		match s1, s2 with
		| Bot, _ -> true
		| _, Top -> true
		| Minus, Minus
		| Zero, Zero
		| Plus, Plus -> true
		| _, _ -> false

	(* least upper bound (CPO) *)
	let lub: t -> t -> t
	= fun s1 s2 ->
		if s1 = s2 then s1
		else
			match s1, s2 with
			| Bot, _ -> s2
			| _, Bot -> s1
			| _, _ -> Top

	let add: t -> t -> t
	= fun s1 s2 ->
		match s1, s2 with
		| Bot, _
		| _, Bot -> Bot
		| Top, _
		| _, Top -> Top
		| Plus, Plus
		| Plus, Zero
		| Zero, Plus -> Plus
		| Minus, Minus
		| Minus, Zero
		| Zero, Minus -> Minus
		| Zero, Zero -> Zero
		| _, _ -> Top

	let equal: t -> t -> t
	= fun s1 s2 ->
		match s1, s2 with
		| Bot, _ 
		| _, Bot -> Bot
		| Zero, Zero -> Plus
		| x, y when x <> y -> Zero
		| _, _ -> Top

	let less s1 s2 =
	 match s1, s2 with
	 | Bot, _ | _, Bot -> Bot
	 | Zero, Zero -> Zero
	 | Minus, Plus | Zero, Plus | Minus, Zero -> Plus
	 | Plus, Minus | Plus, Zero | Zero, Minus -> Zero
	 | _, _ -> Top

	let not s =		(* sign의 전환이 아니라 참/거짓 관점에서의 negation을 말하네. *)
		match s with
		| Bot -> Bot
		| Top -> Top
		| Zero -> Plus
		| _ -> Zero

	let to_string: t -> string
	= fun s ->
		match s with
		| Bot -> "Bot"
		| Top -> "Top"
		| Plus -> "+"
		| Minus -> "-"
		| Zero -> "0"
end

module IdMap = Map.Make (String)

(*======================================================================== 
	abstract domain: Memory (CPO)
								 : Var -> Sign
==========================================================================*)
module Memory = struct
	type t = Sign.t IdMap.t		(* t: String.t -> Sign.t *)

	let bot = IdMap.empty

	let find: id -> t -> Sign.t
	= fun x m ->
		try IdMap.find x m
		with Not_found -> Sign.bot

	let add: id -> Sign.t -> t -> t
	= fun x s m -> IdMap.add x s m

	let order: t -> t -> bool
	= fun m1 m2 -> IdMap.for_all (fun x s -> Sign.order s (find x m2)) m1

	let lub: t -> t -> t
	= fun m1 m2 ->
		IdMap.fold (fun x s m ->
			let s' = IdMap.find x m in
			let s'' = Sign.lub s s' in
				IdMap.add x s'' m
		) m1 m2

	let to_string: t -> string
	= fun m ->
		IdMap.fold (fun k v s ->
			s ^ "\n" ^ k ^ " -> " ^ Sign.to_string v
		) m ""
end

(*========================================================================
	abstract semantics: Expression
==========================================================================*)
let rec eval: exp -> Memory.t -> Sign.t
= fun e m ->
	match e with
	| NUM n -> Sign.alpha n
	| VAR x -> Memory.find x m
	| ADD (e1, e2) -> Sign.add (eval e1 m) (eval e2 m)
	| EQUAL (e1, e2) -> Sign.equal (eval e1 m) (eval e2 m)
	| LESS (e1, e2) -> Sign.less (eval e1 m) (eval e2 m)
	| NOT e -> Sign.not (eval e m)

(*========================================================================
	abstract semantics: Statement
==========================================================================*)
let prune: exp -> Memory.t -> Memory.t
= fun e m -> m (* TODO *)

let rec run: stmt -> Memory.t -> Memory.t
= fun s m ->
	match s with
	| READ x -> Memory.add x Sign.Top m
	| WRITE e -> m (* 화면 출력은 그냥 무시 *)
	| ASSIGN (x, e) -> Memory.add x (eval e m) m
	| IF (e, s1, s2) -> Memory.lub (run s1 (prune e m)) (run s2 (prune (NOT e) m))
	| WHILE (e, s) -> prune (NOT e) (fix (run s) (prune e m))  (* TODO: 잘 이해 안됨. *)
	| SEQ (s1, s2) -> run s2 (run s1 m)
	
and fix f m =
	print_endline (Memory.to_string m);
	if Memory.order (f m) m then m
	else fix f (f m)

(*========================================================================
	Start analysis!
==========================================================================*)
let _  = print_endline (Memory.to_string (run p Memory.bot))
