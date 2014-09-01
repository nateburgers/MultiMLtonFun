(* Parallelism Tests (c) Nathan Burgers 2014 *)
signature ACTOR = sig
    type 'a t
    val spawn : ('b -> 'a -> 'b) -> 'b -> 'a t
    val send : 'a t -> 'a -> unit
end

structure Actor :> ACTOR = struct
open MLton.Pacml
type 'a t = 'a chan
fun spawn f x =
    let val pid = channel ()
	fun loop x = loop (f x (recv pid))
	val _ = MLton.Pacml.spawn (fn () => (loop x; ()))
    in pid
    end
fun send p x = aSend (p, x)
end

signature THUNK = sig
    type 'a thunk = unit -> 'a
    val delay : ('a -> 'b) -> 'a -> 'b thunk
    val <- : ('a -> 'b) * 'a -> 'b thunk (* infix delay *)
    val force : 'a thunk -> 'a
    val promise : 'a thunk -> 'a thunk
    val bifurcate : 'a thunk * 'b thunk -> 'a * 'b
    val parallel : 'a thunk list -> 'a list
end

structure Thunk : THUNK = struct
open MLton.Pacml
type 'a thunk = unit -> 'a
fun delay f x () = f x
infix 6 <-
fun f <- x = delay f x
fun force f = f ()
fun promise f = let val chan = channel ()
		    val _ = spawn (fn () => send (chan, force f))
		in fn () => recv chan
		end
fun bifurcate (f, g) = let val f' = promise f
			   val g' = promise g
		       in (force f', force g')
		       end
fun parallel fs = let val promises = map promise fs
		  in map force promises
		  end
end

infix 8 \
infix 7 <<
infixr 7 >>
infix 6 ||
signature PI_CALCULUS = sig
    datatype t = Nil
	       | Variable of string
	       | Channel of t MLton.Pacml.chan
	       | New of string * t
	       | Parallel of t * t
	       | Output of t * t * t
	       | Input of t * t * t
	       | Replicate of t
    val ` : string -> t
    val \ : string * t -> t
    val || : t * t -> t
    val >> : (t * t) * t -> t
    val << : (t * t) * t -> t
    val !! : t -> t
    val replace : t -> string -> t -> t
    val toString : t -> string
end

structure PiCalculus : PI_CALCULUS = struct
open MLton.Pacml
datatype t = Nil
	   | Variable of string
	   | Channel of t chan
	   | New of string * t
	   | Parallel of t * t
	   | Output of t * t * t
	   | Input of t * t * t
	   | Replicate of t
fun `x = Variable x
fun v \ p = New (v, p)
fun p || q = Parallel (p, q)
fun (c, v) >> p = Output (v, c, p)
fun (c, v) << p = Input (v, c, p)
fun !! p = Replicate p


fun replace Nil x r = Nil
  | replace (Variable v) x r = if v = x
			       then r
			       else Variable v
  | replace (Channel c) x r = Channel c
  | replace (New (v, c)) x r = if v = x
			      then New (v, c)
			      else New (v, (replace c x r))
  | replace (Parallel (p, q)) x r = Parallel ( replace p x r
					     , replace q x r
					     )
  | replace (Output (v, c, p)) x r = Output ( replace v x r
					    , replace c x r
					    , replace p x r
					    )
  | replace (Input (v, c, p)) x r = Input ( replace v x r
					  , replace c x r
					  , replace p x r
					  )
  | replace (Replicate p) x r = Replicate (replace p x r)

exception Evaluate 
val rec evaluate =
 fn Nil => Nil
  | Variable v => raise Evaluate
  | New (v, c) => let val chan = Channel channel
		      val c' = replace c v chan
		  in evaluate c'
		  end
  | Channel c => Channel c
  | Parallel (p, q) => let val pChan = channel
			   val qChan = channel
			   val _ = spawn (fn () =>
					     aSend (pChan, evaluate p))
			   val _ = spawn (fn () =>
					     aSend (qChan, evaluate q))
			   val p' = recv pChan
			   val q' = recv qChan
		       in case p' & q' of
			      (Nil, value) => value
			    | (value, Nil) => value
			    | both => both
		       end
  | Output (v, c, p) => (case evaluate c of
			     Channel chan =>
			     let val v' = evaluate v
				 val () = aSend (chan, v')
			     in evaluate p
			     end
			   | other => raise Evaluate
			)
  | Input (v, c, p) => (case evaluate c of
			    Channel chan =>
			    let val input = recv chan
				val v' = evaluate v
				val p' = replace p v input
			    in evaluate p'
			    end
			  | other => raise Evaluate
		       )
  | Replicate p => raise Evaluate (* TODO: replace with recursion? *)

val rec toString =
 fn Nil => "0"
  | Variable v => v
  | Channel chan => "{chan}"
  | New (v, c) => "(new " ^ v ^ ")" ^ toString c
  | Parallel (p, q) => toString p ^ " || " ^ toString q
  | Output (v, c, p) => toString c ^ "<" ^ toString v ^ ">." ^ toString p
  | Input (v, c, p) => toString c ^ "(" ^ toString v ^ ")." ^ toString p
  | Replicate p => "!" ^ toString p
end

open PiCalculus;
val expression = !! ((`"x", `"u") >> (`"x", `"r") >> ((`"r", `"u") << Nil))
val () = TextIO.print (toString expression)

(* signature STREAM = sig *)
(*     type 'a t *)
(*     val unfold : ('b -> 'a * 'b) -> 'b -> 'a t *)
(*     val iterate : ('a -> 'a) -> 'a -> 'a t *)
(* end *)

(* signature SINK = sig *)
(*     type 'a t *)
(*     val fold : ('b * 'a -> 'b) -> 'b -> 'a t *)
(*     val f : ('a -> 'a) -> 'a t *)
(* end *)

(* signature REACTIVE = sig *)
(*     structure Stream : STREAM *)
(*     structure Sink : SINK *)
(* end *)
