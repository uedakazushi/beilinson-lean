import VersoManual
open Verso.Genre Manual
#doc (Manual) "第2章 線束のコホモロジー" =>

# 計算の定理

**定理。** $`X=\mathbb P(V)` に対し $`0<q<n` なら任意の整数 $`d` について
$`H^q(X,\mathcal O(d))=0` であり、
$$`H^0(X,\mathcal O(d))=\begin{cases}\operatorname{Sym}^{d}(V^\vee)&d\geq0,\\0&d<0.\end{cases}`
さらに $`H^n(X,\mathcal O(d))=0` が $`d>-n-1` で成立する（$`n\geq1`）。
特に $`-n\leq d\leq n` なら $`q>0` に対して $`H^q(X,\mathcal O(d))=0` である。

**証明。** 斉次座標 $`x_0,\dots,x_n` と標準開被覆 $`U_i=D_+(x_i)` を取る。
この被覆の有限交叉は affine であるため、線束の層コホモロジーは Čech 複体で計算できる。
複体を斉次有理単項式 $`x_0^{a_0}\cdots x_n^{a_n}`（$`\sum a_i=d`）ごとに分解する。
その単項式が $`U_{i_0}\cap\cdots\cap U_{i_q}` で正則なのは、負指数の添字がすべて集合 $`\{i_0,\ldots,i_q\}` に属するときである。
従って各単項式の部分複体は、負指数の集合が空または全体のときを除き、単体の相対 Čech 複体として非輪状である。
負指数が空なら次数0に非負指数の斉次単項式が残り、$`\operatorname{Sym}^{d}(V^\vee)` になる。
負指数が全体なら次数 $`n` にのみコホモロジーが残り、そのためには $`d\leq-n-1` を要する。
以上で定理が従う。$`n=0` は $`X=\operatorname{Spec}k` から直接従う。証明終。

# Ext の計算

局所自由層の Hom–cohomology 比較により
$$`\operatorname{Ext}^q_X(\mathcal O(i),\mathcal O(j))\cong H^q(X,\mathcal O(j-i)).`
$`0\leq i,j\leq n` とすれば $`-n\leq j-i\leq n` なので $`q>0` の Ext は消滅する。
また $`i>j` のとき $`j-i<0` だから $`\operatorname{Hom}(\mathcal O(i),\mathcal O(j))=0` である。

形式化では、標準被覆の Čech 複体、単項式分解、非輪状性、Ext とコホモロジーの比較を分離する。
