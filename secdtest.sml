
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

open SECD

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

val _ = eval suc []
val _ = eval pred []
val _ = eval plus []
val _ = eval twice []
val _ = eval comp []
val _ = eval recd []
val _ = compile recd

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

val _ = eval fak []
val _ = eval foldri []

