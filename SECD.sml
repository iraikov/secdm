
(* 

 A compiler and interpreter for a small language for arithmetic expressions. 
 Based on code by O Danvy.

 Copyright 2014 Ivan Raikov and the Okinawa Institute of
 Science and Technology.

 This program is free software: you can redistribute it and/or
 modify it under the terms of the GNU General Public License as
 published by the Free Software Foundation, either version 3 of the
 License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 A full copy of the GPL license can be found at
 <http://www.gnu.org/licenses/>.

*)


structure SECD =
struct


type 'a lazy = unit -> 'a
fun force (f:'a lazy) = f () 


type var = Symbol.symbol
type label = Symbol.symbol


datatype expr =
    Int    of int
  | Bool   of bool
  | Real   of real
  | Con    of var * expr list
  | Var    of var
  | Label  of var
  | UnOp   of var * expr
  | BinOp  of var * expr * expr
  | Cond   of expr * expr * expr
  | App    of expr * expr
  | Abs    of var * expr
  | Let    of var * expr * expr
  | LetRec of (var * expr) list * expr
  | Clos   of expr * (expr Symbol.table) lazy


exception NotFound of var


(*  call-by-value interpreter  *)

exception Eval

fun withTuple (sym, f) (Con (c, args)) = 
    (if c=sym then f args else raise Eval)
    | withTuple (_, _) _ = raise Eval


fun rsel fld (Con (fld',[v]) :: rst) =
    if fld=fld' then v else rsel fld rst
  | rsel fld _ = raise Eval


val symbol = Symbol.symbol


val apply1 = 
    foldl (fn ((s,t),e) => Symbol.enter (s,t,e)) 
          Symbol.empty
          [
           (symbol "not", 
            fn (Bool x) => Bool (not x) | _ => raise Eval),
           (symbol "hd",  
            withTuple (symbol "cons", 
                    fn ([x,y]) => x | _ => raise Eval)),
           (symbol "tl",  
            withTuple (symbol "cons", 
                    fn ([x,y]) => y | _ => raise Eval)),
           (symbol "exp", fn (Real x) => Real (Math.exp x)   | _ => raise Eval),
           (symbol "sqrt", fn (Real x) => Real (Math.sqrt x) | _ => raise Eval),
           (symbol "log", fn (Real x) => Real (Math.log10 x) | _ => raise Eval),
           (symbol "sin", fn (Real x) => Real (Math.sin x)   | _ => raise Eval),
           (symbol "cos", fn (Real x) => Real (Math.cos x)   | _ => raise Eval),
           (symbol "tan", fn (Real x) => Real (Math.tan x)   | _ => raise Eval),
           (symbol "asin", fn (Real x) => Real (Math.asin x) | _ => raise Eval),
           (symbol "atan", fn (Real x) => Real (Math.atan x) | _ => raise Eval),
           (symbol "acos", fn (Real x) => Real (Math.acos x) | _ => raise Eval),
           (symbol "sinh", fn (Real x) => Real (Math.sinh x) | _ => raise Eval),
           (symbol "cosh", fn (Real x) => Real (Math.cosh x) | _ => raise Eval),
           (symbol "tanh", fn (Real x) => Real (Math.tanh x) | _ => raise Eval),
           (symbol "abs", fn (Real x) => Real (Real.abs x)   | _ => raise Eval),
           (symbol "sgn", fn (Real x) => Int (Real.sign x)   | _ => raise Eval)
          ]


val apply2 =
    foldl (fn ((s,t),e) => (Symbol.enter (s,t,e))) 
          Symbol.empty
          [
           (symbol "+",
            fn (Int x,Int y)   => Int (x+y) 
             | (Real x,Real y) => Real (Real.+ (x,y))
             | (Int x,Real y)  => Real (Real.+ (Real.fromInt x,y))
             | (Real x,Int y)  => Real (Real.+ (x, Real.fromInt y))
             | _ => raise Eval),
           (symbol "-",
            fn (Int x,Int y)   => Int (x-y) 
             | (Real x,Real y) => Real (Real.- (x,y))
             | (Int x,Real y)  => Real (Real.- (Real.fromInt x,y))
             | (Real x,Int y)  => Real (Real.- (x, Real.fromInt y))
             | _ => raise Eval),
           (symbol "*",
            fn (Int x,Int y)   => Int (x*y) 
             | (Real x,Real y) => Real (Real.* (x,y))
             | (Int x,Real y)  => Real (Real.* (Real.fromInt x,y))
             | (Real x,Int y)  => Real (Real.* (x, Real.fromInt y))
             | _ => raise Eval),
           (symbol ">", 
            fn (Int x,Int y)   => Bool (x>y) 
             | (Real x,Real y) => Bool (Real.> (x,y))
             | (Int x,Real y)  => Bool (Real.> (Real.fromInt x,y))
             | (Real x,Int y)  => Bool (Real.> (x, Real.fromInt y))
             | _ => raise Eval),
           (symbol "<", 
            fn (Int x,Int y)   => Bool (x<y) 
             | (Real x,Real y) => Bool (Real.< (x,y))
             | (Int x,Real y)  => Bool (Real.< (Real.fromInt x,y))
             | (Real x,Int y)  => Bool (Real.< (x, Real.fromInt y))
             | _ => raise Eval),
           (symbol "=",
            let
                fun eq (Int x,Int y) = Bool (x=y)
                  | eq (Bool x,Bool y) = Bool (x=y)
                  | eq (Real x,Real y) = Bool (Real.==(x,y))
                  | eq (Con (c,ls), Con (c',ls')) = Bool (c=c' andalso alleq (ls,ls'))
                  | eq (_, _) = Bool(false)
                                      
                and alleq (ls,ls') = 
                    ListPair.all
                        (fn (l,l') => case eq (l,l') of Bool b => b | _ => raise Eval)
                        (ls,ls')
            in
                eq
            end),
           (symbol "rsel",
            fn (Label fld, Con (c,rst)) =>
               (if (c=symbol "$")  
                then rsel fld rst else raise Eval)
             | _ => raise Eval)
          ]



fun def E Efun (x,Abs (y,e)) = (x,Clos (Abs (y,e),Efun))
 |  def E Efun (x,e)         = (x,eval e E)


and eval (Int i)           E = Int i
 |  eval (Bool b)          E = Bool b
 |  eval (Real r)          E = Real r
 |  eval (Label l)         E = Label l
 |  eval (Con (c,l))       E = Con (c,map (fn x=>eval x E) l)
 |  eval (Var x)           E = (case Symbol.lookup (x,E) of 
                                    SOME v => v | NONE => raise Eval)
 |  eval (UnOp (f,e))      E = (case Symbol.lookup (f, apply1) of 
                                    SOME proc => proc (eval e E) 
                                  | NONE => raise Eval)
 |  eval (BinOp (f,e1,e2)) E = (case Symbol.lookup (f, apply2) of 
                                    SOME proc => proc (eval e1 E, eval e2 E)
                                  | NONE => raise Eval)
 |  eval (Cond (e,e1,e2))  E = (let 
                                    val v = eval e E 
                                in
                                    eval (case v of 
                                              Bool b => if b then e1 else e2
                                            | _ => raise Eval) E
                                end)
 |  eval (App (e,e'))      E =  
    let 
        val v = eval e E
    in
        case v of
            Clos (Abs (x,e''),E') =>
            eval e'' (Symbol.enter (x,eval e' E,force E'))
          | _ => raise Eval
    end
 |  eval (Abs (x,e))       E = Clos (Abs (x,e),fn ()=>E)
 |  eval (Let (x,e,e'))    E = eval e' (Symbol.enter (x,eval e E,E))
 |  eval (LetRec (d,e))    E = 
    let 
        fun NewE () = Symbol.enter' (map (def E NewE) d, E)
    in
        eval e (force NewE)
    end
 | eval  _ _ = raise Eval



(* dummy datatype for representing normal values and 
   updateable dummy entries in environments *)
   
datatype 'a dummy = 
   Val of 'a
 | Dum of 'a ref


fun norm (Val x) = x
 |  norm (Dum x) = !x



(* values and operations of the SECD machine *)

datatype value =
    I  of int
  | B  of bool
  | R  of real
  | T  of label * value list
  | CL of label * code list * value dummy list
  | UNDEF


and code = 
    LD   of value (* pushes a literal onto the stack *)
  | LDV  of int   (* pushes the value of a variable onto the stack *)
  | LDC  of label * code list (* pushes a closure onto the stack *)
  | LDT  of label * int
  | APP  
  | RAP  of int  (* recursive app; replaces the dummy environment with the current one *)
  | DUM  of int  (* puts a dummy empty environment in front of the env list *)
  | COND of code list * code list
  | RET
  | ADD | SUB | MULT | NOT | EQ | LT | GT | HD | TL | RSEL of label
  | EXP | SQRT | LOG | SIN | TAN | COS | ASIN | ATAN | ACOS | SINH | TANH | COSH | ABS | SGN    


fun vequal (I i, I i') = i=i'
  | vequal (B b, B b') = b=b'
  | vequal (R r, R r') = (Real.== (r,r'))
  | vequal (T (s,vs), T (s',vs')) =
    (s=s' andalso ListPair.allEq vequal (vs,vs') )
  | vequal (UNDEF, UNDEF) = true
  | vequal (_, _) = false


fun valueString v =
    case v of 
        I i => ("I " ^ (Int.toString i))
      | B b => if b then "true" else "false"
      | R r => ("R " ^ (Real.toString r))
      | T (c,lst) => ("T [" ^ (Symbol.name c) ^ "](" ^
                      (String.concatWith "," (map valueString lst)) ^ ")")
      | CL (l,_,_) => "CL " ^ (Symbol.name l)
      | UNDEF => "UNDEF"

fun codeString c =
    case c of 
        LD v      => ("LD " ^ (valueString v))
      | LDV i     => ("LDV " ^ (Int.toString i))    
      | LDC (l,cl) => ("LDC (" ^ (Symbol.name l) ^ ") [" ^ (String.concatWith ", " (map codeString cl)) ^ "]") 
      | LDT (l,i) => ("LDT (" ^ (Symbol.name l) ^ ", " ^ (Int.toString i) ^ ")")
      | APP       =>  ("APP")
      | RAP i     =>  ("RAP " ^ (Int.toString i))
      | DUM i     =>  ("DUM " ^ (Int.toString i))
      | COND (cl1,cl2)  =>  ("COND [" ^ (String.concatWith ", " (map codeString cl1)) ^ 
                             ", " ^ (String.concatWith ", " (map codeString cl2)) ^ "]")
      | RET       =>  ("RET")
      | _         =>  ("PRIM")


val take = List.take
val drop = List.drop

(* some auxiliary functions:
   index    selects kth element of a list
   mkdummy  creates a new environment with n updateable entries at the front
   upddummy updates dummy entries
*)
   
fun index 1 (x::l) = x
 |  index k (x::l) = index (k-1) l
 |  index _ _ = raise Match

fun mkdummy 0 E = E
 |  mkdummy n E = mkdummy (n-1) (Dum (ref UNDEF)::E)

fun upddummy [] E              = ()
 |  upddummy (x::l) (Dum v::E) = (v:=x; upddummy l E)
 |  upddummy _ _ = raise Match


fun rselv fld (T (fld',[v]) :: rst) =
    if fld=fld' then v else rselv fld rst
  | rselv fld _ = raise Match

(*  SECD transitions  *)

exception Machine

fun checkTuple (c, sym) = 
    case Symbol.compare (c,sym) of
        EQUAL => ()
      | _ => raise Machine

fun alop (code, x, y) =
    case (code,x,y) of
        (ADD, I x, I y)   => (I (x+y))
      | (ADD, I x, R y)   => (R (Real.+(Real.fromInt x, y)))
      | (ADD, R x, I y)   => (R (Real.+(x,Real.fromInt y)))
      | (ADD, R x, R y)   => (R (Real.+(x,y)))
      | (SUB, I x, I y)   => (I (x-y))
      | (SUB, I x, R y)   => (R (Real.-(Real.fromInt x, y)))
      | (SUB, R x, I y)   => (R (Real.-(x,Real.fromInt y)))
      | (SUB, R x, R y)   => (R (Real.-(x,y)))
      | (MULT, I x, I y)  => (I (x*y))
      | (MULT, I x, R y)  => (R (Real.*(Real.fromInt x, y)))
      | (MULT, R x, I y)  => (R (Real.*(x,Real.fromInt y)))
      | (MULT, R x, R y)  => (R (Real.*(x,y)))
      | (LT, I x, I y)    => (B (x<y))
      | (LT, I x, R y)    => (B (Real.<(Real.fromInt x, y)))
      | (LT, R x, I y)    => (B (Real.<(x,Real.fromInt y)))
      | (LT, R x, R y)    => (B (Real.<(x,y)))
      | (GT, I x, I y)    => (B (x>y))
      | (GT, I x, R y)    => (B (Real.>(Real.fromInt x, y)))
      | (GT, R x, I y)    => (B (Real.>(x,Real.fromInt y)))
      | (GT, R x, R y)    => (B (Real.>(x,y)))
      | (_, _, _)         => raise Machine


fun mathop (code, x) =
    case (code, x) of
        (EXP,  x) => R (Math.exp x)
      | (SQRT, x) => R (Math.sqrt x)
      | (LOG, x) => R (Math.log10 x)
      | (SIN, x) => R (Math.sin x)
      | (COS, x) => R (Math.cos x)
      | (TAN, x) => R (Math.tan x)
      | (ASIN, x) => R (Math.asin x)
      | (ACOS, x) => R (Math.acos x)
      | (ATAN, x) => R (Math.atan x)
      | (SINH, x) => R (Math.sinh x)
      | (TANH, x) => R (Math.tanh x)
      | (COSH, x) => R (Math.cosh x)
      | (ABS, x) => R (Real.abs x)
      | (SGN, x) => I (Real.sign x)
      | (_, _) => raise Machine
                   

fun step (S,E,LD  x::C,D)                 = (x::S,E,C,D)
 |  step (S,E,LDV k::C,D)                 = (norm (index k E)::S,E,C,D)
 |  step (S,E,LDC (l,C')::C,D)            = (CL (l,C',E)::S,E,C,D)
 |  step (S,E,LDT (c,n)::C,D)             = (T (c,rev (take (S,n)))::(drop (S,n)),E,C,D)
 |  step (CL (_,C',E')::x::S,E,APP::C,D)  = ([],Val x::E',C',(S,E,C)::D)
 |  step (y::x::S,E, ADD::C,D)            = (alop (ADD,x,y)::S,E,C,D)
 |  step (y::x::S,E, SUB::C,D)            = (alop (SUB,x,y)::S,E,C,D)
 |  step (y::x::S,E,MULT::C,D)            = (alop (MULT,x,y)::S,E,C,D)
 |  step (y::x::S,E,  LT::C,D)            = (alop (LT,x,y)::S,E,C,D)
 |  step (y::x::S,E,  GT::C,D)            = (alop (GT,x,y)::S,E,C,D)
 |  step (y::x::S,E,  EQ::C,D)            = (B (vequal (x,y))::S,E,C,D)
 |  step (R x::S,E, oper::C,D)            = ((mathop (oper,x))::S,E,C,D)
 |  step (B x::S,E,  NOT::C,D)            = (B (not x)::S,E,C,D)
 |  step (T (c,[x,y])::S,E,HD::C,D)       = (checkTuple (c, symbol "cons"); (x::S,E,C,D))
 |  step (T (c,[x,y])::S,E,TL::C,D)       = (checkTuple (c, symbol "cons"); (y::S,E,C,D))
 |  step (T (c,rst)::S,E,(RSEL s)::C,D)   = (checkTuple (c, symbol "$"); ((rselv s rst)::S,E,C,D))
 |  step (B true::S, E,COND (C1,C2)::C,D) = (S,E,C1,([],[],C)::D)
 |  step (B false::S,E,COND (C1,C2)::C,D) = (S,E,C2,([],[],C)::D)
 |  step (S,E,[RET],(_,_,C)::D)           = (S,E,C,D)
 |  step (S,E,DUM n::C,D)                 = (S,mkdummy n E,C,D)
 |  step (CL (l,C',E')::S,E,RAP n::C,D)   = (upddummy (rev (take (S,n))) E; 
                                             (S,E,C',(drop (S,n),drop (E,n),C)::D))
 |  step (x::S,E,[],(S',E',C')::D)        = (x::S',E',C',D)
 |  step (S,E,C,D)                        = raise Machine



fun loop (S,E,[],[]) = S
 |  loop state = loop (step state)
 
fun secd C = loop ([],[],C,[])



(* SECD compiler *)

exception Prim

val prim =
    foldl (fn ((s,t),e) => Symbol.enter (s,t,e)) 
          Symbol.empty
          [
           (symbol "+",   ADD),
           (symbol "-",   SUB),
           (symbol "*",   MULT),
           (symbol "=",   EQ),
           (symbol ">",   GT),
           (symbol "<",   LT),
           (symbol "not", NOT),
           (symbol "hd",  HD),
           (symbol "tl",  TL),
           (symbol "exp", EXP),
           (symbol "sqrt", SQRT),
           (symbol "log", LOG),
           (symbol "sin", SIN),
           (symbol "cos", COS),
           (symbol "tan", TAN),
           (symbol "asin", ASIN),
           (symbol "atan", ATAN),
           (symbol "acos", ACOS),
           (symbol "sinh", SINH),
           (symbol "cosh", COSH),
           (symbol "tanh", TANH),
           (symbol "abs", ABS),
           (symbol "sgn", SGN)
          ]


fun position x (y::l) = 1+(if x=y then 0 else position x l)
  | position x _ = raise Match


fun listConcat l = foldr op@ [] l 


exception Compiler


fun compile (Int i)           N = [LD (I i)]
 |  compile (Bool b)          N = [LD (B b)]
 |  compile (Real r)          N = [LD (R r)]
 |  compile (Var x)           N = [LDV (position x N)]
 |  compile (Con (c,l))       N = listConcat (map (fn e=>compile e N) l)@[LDT (c,length l)]
 |  compile (UnOp (f,e))      N = let val fv = Symbol.lookup (f,prim)
                                  in 
                                      case fv of
                                          SOME v => compile e N@[v]
                                        | NONE => raise Compiler
                                  end
 |  compile (BinOp (f,Label s,e)) N = if f=symbol "rsel"
                                      then compile e N@[(RSEL s)]
                                      else raise Compiler
 |  compile (BinOp (f,e1,e2)) N = let val fv = Symbol.lookup (f,prim)
                                  in 
                                      case fv of
                                          SOME v => compile e1 N@compile e2 N@[v]
                                        | NONE => raise Compiler
                                  end
 |  compile (Cond (e,e1,e2))  N = compile e N@[COND (compile e1 N@[RET],compile e2 N@[RET])]
 |  compile (Abs (x,e))       N = [LDC (Symbol.fresh "f", compile e (x::N))]
 |  compile (App (e,e'))      N = compile e' N@compile e N@[APP]
 |  compile (Let (x,e,e'))    N = compile e N@[LDC (Symbol.fresh "l", compile e' (x::N)),APP]
 |  compile (LetRec (d,e))    N = let val n = length d
                                      val N' = map #1 d@N
                                      val ci = listConcat (map (fn (v,e)=>compile e N') d)
                                  in
                                      DUM n::ci@[LDC (Symbol.fresh "r", compile e N'),RAP n]
                                  end
 |  compile (Clos (_,_))    N = raise Compiler
 |  compile (Label _)       N = raise Compiler


end
