
(* A compiler and interpreter for a small language for arithmetic expressions. 
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

type 'a lazy = unit -> 'a
fun force (f:'a lazy) = f () 

type var = string

datatype expr =
    Int    of int
  | Bool   of bool
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
  | Clos   of expr * env lazy

withtype env  = (var * expr) list



exception NotFound of var

fun ins l E = l@E
fun lookup (x,(y,e)::E) = if x=y then e else lookup (x,E)
  | lookup (x,[]) = raise NotFound x



(*  call-by-value interpreter  *)

exception Eval

fun apply1 "not" (Bool x)             = Bool (not x)
 |  apply1 "hd"  (Con ("cons",[x,y])) = x
 |  apply1 "tl"  (Con ("cons",[x,y])) = y
 |  apply1 _  _ = raise Eval

fun apply2 "+" (Int x,Int y) = Int (x+y)
 |  apply2 "-" (Int x,Int y) = Int (x-y)
 |  apply2 "*" (Int x,Int y) = Int (x*y)
 |  apply2 ">" (Int x,Int y) = Bool (x>y)
 |  apply2 "<" (Int x,Int y) = Bool (x<y)
 |  apply2 "=" (Int x,Int y) = Bool (x=y)
 |  apply2 "=" (Bool x,Bool y) = Bool (x=y)
 |  apply2 "=" (Con (c,l), Con (c',l')) = Bool (c=c' andalso alleq (l,l'))
 |  apply2 "rsel"  (Label fld, Con ("$",rst)) = rsel fld rst
 |  apply2 _ _ = raise Eval

and rsel fld (Con (fld',[v]) :: rst) =
    if fld=fld' then v else rsel fld rst
  | rsel fld _ = raise Eval

and alleq ([],[]) = true
 |  alleq (x::l,y::l') = 
    let
        val v = (apply2 "=" (x,y))
    in
        (case v of Bool b => b | _ => raise Eval)  andalso alleq (l,l')
    end
 | alleq (_,_) = raise Eval

fun def E Efun (x,Abs (y,e)) = (x,Clos (Abs (y,e),Efun))
 |  def E Efun (x,e)         = (x,eval e E)

and eval (Int i)           E = Int i
 |  eval (Bool b)          E = Bool b
 |  eval (Label l)         E = Label l
 |  eval (Con (c,l))       E = Con (c,map (fn x=>eval x E) l)
 |  eval (Var x)           E = lookup (x,E)
 |  eval (UnOp (f,e))      E = apply1 f (eval e E)
 |  eval (BinOp (f,e1,e2)) E = apply2 f (eval e1 E,eval e2 E)
 |  eval (Cond (e,e1,e2))  E = let val v = eval e E 
                               in
                                   eval (case v of 
                                             Bool b => if b then e1 else e2
                                           | _ => raise Eval) E
                               end
 |  eval (App (e,e'))      E =  
    let val v = eval e E
    in
        case v of
            Clos (Abs (x,e''),E') =>
            eval e'' (ins [(x,eval e' E)] (force E'))
          | _ => raise Eval
    end
 |  eval (Abs (x,e))       E = Clos (Abs (x,e),fn ()=>E)
 |  eval (Let (x,e,e'))    E = eval e' (ins [(x,eval e E)] E)
 |  eval (LetRec (d,e))    E = 
         let fun NewE () = ins (map (def E NewE) d) E
          in
             eval e (force NewE)
         end
 | eval  _ _ = raise Eval


(* examples *)

(* simple functions *)
val suc   = Abs ("x",BinOp ("+",Var "x",Int 1));
val pred  = Abs ("x",BinOp ("-",Var "x",Int 1));
val plus  = Abs ("x",Abs ("y",BinOp ("+",Var "x",Var "y")));
val twice = Abs ("f",Abs ("x",App (Var "f", App (Var "f",Var "x"))));
val comp  = Abs ("f",Abs ("g",Abs ("x",App (Var "f", App (Var "g",Var "x")))));

val recd  = BinOp ("rsel",
                   Label "x", 
                   Con ("$", [Con ("x",[BinOp ("+",Int 1,Int 2)]),
                              Con ("y",[BinOp ("+",Int 3,Int 4)])]))

val _ = eval recd []

(* recursive functions *)
val fak   = LetRec (
             [("f",Abs ("x",Cond (BinOp ("<",Var "x",Int 2),Int 1,
                             BinOp ("*",Var "x", 
                               App (Var "f",BinOp("-",Var "x",Int 1))))))],
             Var "f")
val foldri = LetRec (
             [("g",Abs ("f", Abs ("u", Abs ("l",
                   Cond (BinOp ("=",Var "l",Con ("nil",[])),
                               Var "u",
                               App (App (Var "f",UnOp ("hd",Var "l")),
                                    App (App (App (Var "g",Var "f"),Var "u"),
                                         UnOp ("tl",Var "l"))
                                      ))))))],
             Var "g")
;



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
  | T  of string * value list
  | CL of code list * value dummy list
  | UNDEF

and code = 
    LD   of value (* pushes the value of a variable onto the stack *)
  | LDV  of int   (* pushes an integer literal onto the stack *)
  | LDC  of code list (* pushes a closure onto the stack *)
  | LDT  of string * int
  | APP  (* pops a closure from the stack and a list of parameter values, 
            then applies the parameters to the closure *)
  | RAP  of int  (* recursive app; replaces the dummy environment with the current one *)
  | DUM  of int  (* puts a dummy empty environment in front of the env list *)
  | COND of code list * code list
  | RET (* pops one return value from the stack, restores S, E, and C from the dump *)
  | ADD | SUB | MULT | NOT | EQ | LT | GT | HD | TL | RSEL of string



(* some auxiliary functions:
   index    selects kth element of a list
   mkdummy  creates a new environment with n updateable entries at the front
   upddummy updates dummy entries
   revi     gets the first n elements of a list in reverse order
   popi     drops the first n elements of a list *)
   
fun index 1 (x::l) = x
 |  index k (x::l) = index (k-1) l
 |  index _ _ = raise Match

fun revi 0 l      = l
 |  revi n (x::l) = revi (n-1) l@[x]
 |  revi _ _ = raise Match
 
fun popi 0 l      = l
 |  popi n (x::l) = popi (n-1) l
 |  popi _ _ = raise Match

fun mkdummy 0 E = E
 |  mkdummy n E = mkdummy (n-1) (Dum (ref UNDEF)::E)

fun upddummy [] E              = ()
 |  upddummy (x::l) (Dum v::E) = (v:=x; upddummy l E)
 | upddummy _ _ = raise Match


fun rselv fld (T (fld',[v]) :: rst) =
    if fld=fld' then v else rselv fld rst
  | rselv fld _ = raise Match

(*  SECD transitions  *)

exception Machine


fun step (S,E,LD  x::C,D)                 = (x::S,E,C,D)
 |  step (S,E,LDV k::C,D)                 = (norm (index k E)::S,E,C,D)
 |  step (S,E,LDC C'::C,D)                = (CL (C',E)::S,E,C,D)
 |  step (S,E,LDT (c,n)::C,D)             = (T (c,revi n S)::popi n S,E,C,D)
 |  step (CL (C',E')::x::S,E,APP::C,D)    = ([],Val x::E',C',(S,E,C)::D)
 |  step (x::S,E,[],(S',E',C')::D)        = (x::S',E',C',D)
 |  step (I y::I x::S,E, ADD::C,D)        = (I (x+y)::S,E,C,D)
 |  step (I y::I x::S,E, SUB::C,D)        = (I (x-y)::S,E,C,D)
 |  step (I y::I x::S,E,MULT::C,D)        = (I (x*y)::S,E,C,D)
 |  step (I y::I x::S,E,  LT::C,D)        = (B (x<y)::S,E,C,D)
 |  step (I y::I x::S,E,  GT::C,D)        = (B (x>y)::S,E,C,D)
 |  step (y::x::S,E,      EQ::C,D)        = (B (x=y)::S,E,C,D)
 |  step (B x::S,E,      NOT::C,D)        = (B (not x)::S,E,C,D)
 |  step (T ("cons",[x,y])::S,E,HD::C,D)  = (x::S,E,C,D)
 |  step (T ("cons",[x,y])::S,E,TL::C,D)  = (y::S,E,C,D)
 |  step (T ("$",rst)::S,E,(RSEL s)::C,D) = ((rselv s rst)::S,E,C,D)
 |  step (B true::S, E,COND (C1,C2)::C,D) = (S,E,C1,([],[],C)::D)
 |  step (B false::S,E,COND (C1,C2)::C,D) = (S,E,C2,([],[],C)::D)
 |  step (S,E,[RET],(_,_,C)::D)           = (S,E,C,D)
 |  step (S,E,DUM n::C,D)                 = (S,mkdummy n E,C,D)
 |  step (CL (C',E')::S,E,RAP n::C,D)     = 
         (upddummy (revi n S) E; (S,E,C',(popi n S,popi n E,C)::D))
 |  step (S,E,C,D)                 = raise Machine

fun loop (S,E,[],[]) = S
 |  loop state = loop (step state)
 
fun secd C = loop ([],[],C,[])



(* SECD compiler *)

exception Cmd

fun cmd "+"   = ADD
 |  cmd "-"   = SUB
 |  cmd "*"   = MULT
 |  cmd "="   = EQ
 |  cmd ">"   = GT
 |  cmd "<"   = LT
 |  cmd "not" = NOT
 |  cmd "hd"  = HD
 |  cmd "tl"  = TL
 |  cmd _     = raise Cmd

fun position x (y::l) = 1+(if x=y then 0 else position x l)
  | position x _ = raise Match

fun listConcat l = foldr op@ [] l 

exception Compiler

fun compile (Int i)           N = [LD (I i)]
 |  compile (Bool b)          N = [LD (B b)]
 |  compile (Var x)           N = [LDV (position x N)]
 |  compile (Con (c,l))       N = 
      listConcat (map (fn e=>compile e N) l)@[LDT (c,length l)]
 |  compile (UnOp (f,e))      N = compile e N@[cmd f]
 |  compile (BinOp ("rsel",Label s,e)) N = compile e N@[(RSEL s)]
 |  compile (BinOp (f,e1,e2)) N = compile e1 N@compile e2 N@[cmd f]
 |  compile (Cond (e,e1,e2))  N = 
      compile e N@[COND (compile e1 N@[RET],compile e2 N@[RET])]
 |  compile (App (e,e'))      N = compile e' N@compile e N@[APP]
 |  compile (Abs (x,e))       N = [LDC (compile e (x::N))]
 |  compile (Let (x,e,e'))    N = compile e N@[LDC (compile e' (x::N)),APP]
 |  compile (LetRec (d,e))    N = 
    let val  n = length d
        val N' = map #1 d@N
        val ci = listConcat (map (fn (v,e)=>compile e N') d)
     in
        DUM n::ci@[LDC (compile e N'),RAP n]
    end
 |  compile (Clos (_,_))    N = raise Compiler
 |  compile (Label _)       N = raise Compiler

val _ = compile recd
