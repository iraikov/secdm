
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

fun timing (action) = 
    let
        val timer = Timer.startCPUTimer ()
        val result = action ()
        val times = Timer.checkCPUTimer timer
    in
        (result, Time.+ (#usr times, #sys times))
    end

fun putStrLn (file, str) = 
    (TextIO.output (file, str);
     TextIO.output (file, "\n"))
    
fun putStr (file, str) = 
    (TextIO.output (file, str))

open SECD

val $ = Symbol.symbol

fun etoInt v = case v of Int i => i | _ => raise Match

fun eapp f v = 
    case v of Con (c,[x,y]) => 
              if c=($ "cons") 
                then (f x; eapp f y) else raise Match
            | Con (c,[]) =>
              if c=($ "nil") then () else raise Match
            | _ => raise Match

fun vtoInt v = case v of I i => i | _ => raise Match

fun vapp f v = 
    case v of T (c,[x,y]) => 
              if c=($ "cons") 
                then (f x; vapp f y) else raise Match
            | T (c,[]) =>
              if c=($ "nil") then () else raise Match
            | _ => raise Match
                                     



(* simple functions *)
val suc   = Abs ($ "x",BinOp ($ "+",Var ($ "x"),Int 1));
val pred  = Abs ($ "x",BinOp ($ "-",Var ($ "x"),Int 1));
val plus  = Abs ($ "x",Abs ($ "y",BinOp ($ "+",Var ($ "x"),Var ($ "y"))));
val twice = Abs ($ "f",Abs ($ "x",App (Var ($ "f"), App (Var ($ "f"),Var ($ "x")))));
val comp  = Abs ($ "f",Abs ($ "g",Abs ($ "x",App (Var ($ "f"), App (Var ($ "g"),Var ($ "x"))))));

val recd1 = BinOp ($ "rsel",
                   Label ($ "x"), 
                   Con ($ "$", [Con ($ "x",[BinOp ($ "+",Int 1,Int 2)]),
                                Con ($ "y",[BinOp ($ "+",Int 3,Int 4)])]))

val recd2 = Let ($ "f", Abs ($ "r", BinOp ($ "rsel", Label ($ "x"), Var ($ "r"))),
                 App (Var ($ "f"),
                      Con ($ "$", [Con ($ "x",[BinOp ($ "+",Int 1,Int 2)]),
                                   Con ($ "y",[BinOp ($ "+",Int 3,Int 4)])])))

val math1   = UnOp ($ "sin",Real 60.0);

val E = Symbol.empty

val _ = eval suc E
val _ = eval pred E
val _ = eval plus E
val _ = eval twice E
val _ = eval comp E

val _ = case eval recd1 E of
            Int i => print ("eval recd1 = " ^ (Int.toString i) ^ "\n")
val _ = case eval recd2 E of
            Int i => print ("eval recd1 = " ^ (Int.toString i) ^ "\n")
val _ = case eval math1 E of
            Real r => print ("eval math1 = " ^ (Real.toString r) ^ "\n")

val _ = let val insns = compile math1 []
            val res :: _ = secd insns
        in
            putStrLn (TextIO.stdOut, "secd math1 = " ^ (valueString res))
        end

val _ = let val insns = compile recd1 []
            val res :: _ = secd insns
        in
            putStrLn (TextIO.stdOut, "secd recd1 = " ^ (valueString res))
        end

val _ = let val insns = compile recd2 []
            val res :: _ = secd insns
        in
            putStrLn (TextIO.stdOut, "secd recd2 = " ^ (valueString res))
        end

(* recursive functions *)
val fak   = LetRec 
                (
                 [($ "f",Abs ($ "x",Cond (BinOp ($ "<",Var ($ "x"),Int 2),Int 1,
                                          BinOp ($ "*",Var ($ "x"), 
                                                 App (Var ($ "f"),BinOp($ "-",Var ($ "x"),Int 1))))))],
                 Var ($ "f")
                )
val foldri = LetRec 
                 (
                  [($ "g", Abs ($ "f", Abs ($ "u", Abs ($ "l", Cond (BinOp ($ "=",Var ($ "l"),Con ($ "nil",[])),
                               Var ($ "u"),
                               App (App (Var ($ "f"), UnOp ($ "hd", Var ($ "l"))),
                                    App (App (App (Var ($ "g"), Var ($ "f")), Var ($ "u")),
                                         UnOp ($ "tl", Var ($ "l")))
                                      ))))))],
                  Var ($ "g")
                 )
val tabulate = LetRec 
                   (
                    [($ "g", 
                      Abs ($ "l", 
                           Abs ($ "f", 
                                Abs ($ "n", 
                                     Cond (BinOp ($ "=",Var ($ "n"),Int 0),
                                           Var ($ "l"),
                                           (App
                                                (App
                                                     (App (Var ($ "g"), 
                                                           (Con ($ "cons", 
                                                                 [App (Var ($ "f"), Var ($ "n")), 
                                                                  Var ($ "l")]))),
                                                      Var ($ "f")),
                                                 BinOp ($ "-", Var ($ "n"), Int 1)))
                                    ))
                          ))
                    )],
                    App (Var ($ "g"), Con ($ "nil",[]))
                   )

val fak1 = Let ($ "fak", fak, (App (Var ($ "fak"), Int 10)))

val _ = case eval fak1 E of
            Int i => print ("eval fak1 = " ^ (Int.toString i) ^ "\n")

val _ = let val insns = compile fak1 []
            val res :: _ = secd insns
        in
            putStrLn (TextIO.stdOut, "secd fak1 = " ^ (valueString res))
        end

val tabulate1 = Let ($ "tabulate", tabulate,
                     (App
                      (App (Var ($ "tabulate"),
                            Abs ($ "i", BinOp ($ "*", Var ($ "i"), Int 10))),
                       Int 10000))
                     )

val _ = eval fak E
val _ = compile fak []

val _ = eval foldri E
val _ = compile foldri []

val _ = eval tabulate E
val _ = compile tabulate []

val (t,ti) = timing (fn () => (eapp ((fn i => putStr (TextIO.stdOut, ((Int.toString i) ^ " "))) o etoInt) 
                                     (eval tabulate1 E);
                               putStrLn (TextIO.stdOut, "")))
val _ = print ("tabulate example evaluation took " ^ (Time.toString ti) ^ " s\n")

val (t,ti) = timing (fn () => (let 
                                   val insns = compile tabulate1 []
                                   val res :: _ = secd insns
                               in
                                   (vapp ((fn s => putStr (TextIO.stdOut, (s ^ " "))) o valueString) res;
                                    putStrLn (TextIO.stdOut, ""))
                               end))

val _ = print ("compiled tabulate example simulation took " ^ (Time.toString ti) ^ " s\n")

