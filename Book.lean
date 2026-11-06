import VersoManual
import Book.Introduction
import Book.Cohomology
import Book.Diagonal
import Book.Exceptional
import Book.Quiver
import Book.Tilting
import Book.Examples
import Book.Formalization
open Verso.Genre Manual
#doc (Manual) "Beilinson の定理：射影空間から箙へ" =>
%%%
authors := ["Kazushi Ueda"]
%%%
自然言語による証明を先に完成させ、後から Lean 4 で各補題を形式化する教科書。
現段階の本文は Lean による数学的証明の検証を意味しない。

{include 1 Book.Introduction}
{include 1 Book.Cohomology}
{include 1 Book.Diagonal}
{include 1 Book.Exceptional}
{include 1 Book.Quiver}
{include 1 Book.Tilting}
{include 1 Book.Examples}
{include 1 Book.Formalization}
