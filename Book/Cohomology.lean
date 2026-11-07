import VersoManual
open Verso.Genre Manual
#doc (Manual) "第2章 線束のコホモロジー" =>

# 計算の定理

**定理。** $`n\geq1` とし、$`X=\mathbb P(V)` に対し $`0<q<n` なら任意の整数 $`d` について
$`H^q(X,\mathcal O(d))=0` であり、
$$`H^0(X,\mathcal O(d))=\begin{cases}\operatorname{Sym}^{d}(V^\vee)&d\geq0,\\0&d<0.\end{cases}`
さらに $`H^n(X,\mathcal O(d))=0` が $`d>-n-1` で成立する（$`n\geq1`）。
特に $`-n\leq d\leq n` なら $`q>0` に対して $`H^q(X,\mathcal O(d))=0` である。

**証明。** 斉次座標 $`x_0,\dots,x_n` と標準開被覆 $`U_i=D_+(x_i)` を取る。
$`S=k[x_0,\ldots,x_n]` とおく。空でない添字集合 $`I` に対し、
$`U_I=\bigcap_{i\in I}U_i` は affine であり、
切断は次のように書ける：
$$`\Gamma(U_I,\mathcal O(d))=(S[x_i^{-1}:i\in I])_d.`
従って、この被覆の Čech 複体は層コホモロジーを計算し、次数 $`0,\ldots,n` にのみ項を持つ。
特に $`q>n` のコホモロジーも零である。

指数 $`\alpha=(a_0,\ldots,a_n)\in\mathbb Z^{n+1}`、$`\sum_i a_i=d` を固定し、
Laurent 単項式 $`x^\alpha=x_0^{a_0}\cdots x_n^{a_n}` を考える。
負指数の添字集合を $`N(\alpha)=\{i:a_i<0\}` とすると、
この単項式が $`U_I` 上の切断として現れる条件は $`N(\alpha)\subseteq I` である。
局所化された多項式環の単項式は基底をなすので、Čech 複体は単項式ごとの部分複体の直和に分かれ、
その項は
$$`C^q_\alpha=\bigoplus_{\substack{|I|=q+1\\N(\alpha)\subseteq I}} k.`
微分は添字を昇順に並べた通常の交代和であり、許されない添字集合の係数は零と読む。
直和はベクトル空間の圏で完全なので、各部分複体のコホモロジーを計算すれば十分である。

**場合1：負指数がないとき。** $`N(\alpha)=\varnothing` なら、$`C^\bullet_\alpha` は
$`n`-単体の通常の cochain 複体である。次数 $`-1` に $`k` を加え、
$`k\to C^0_\alpha` を全頂点への対角写像とすると、augmented complex は可縮になる。
従って元の複体には次数0に $`k` のみが残る。
この場合の単項式は非負指数であり、全体で $`S_d=\operatorname{Sym}^d(V^\vee)` を与える。
$`d<0` ではそのような単項式はない。

**場合2：負指数の集合が空でも全体でもないとき。**
$`j\notin N(\alpha)` を一つ選ぶ。次数を一つ下げる写像を、係数ごとに
$$`(h c)_I=\begin{cases}(-1)^{|\{i\in I:i<j\}|}c_{I\cup\{j\}}&j\notin I,\\0&j\in I\end{cases}`
で定める。ここで $`|I|=q`、$`N(\alpha)\subseteq I` として $`h:C^q_\alpha\to C^{q-1}_\alpha` を読む。
$`N(\alpha)` が空でないため、次数 $`-1` の項は零のままでよい。
$`j` を挿入・削除する項を分け、残る項を交代符号で対にすると $`dh+hd=1` となる。
従って、この場合のコホモロジーは全次数で零である。
場合1の augmented complex の収縮も、同じ式を空集合の係数まで含めて使ったものである。

**場合3：全指数が負のとき。** $`N(\alpha)=\{0,\ldots,n\}` なら、
許される $`I` は全体だけなので、$`C^\bullet_\alpha` は次数 $`n` にある一つの $`k` である。
この場合は $`a_i\leq-1` より $`d\leq-n-1` を要する。
逆にこの範囲では、$`b_i=-a_i-1\geq0` とおくと $`\sum_i b_i=-d-n-1` であり、
その個数は $`\binom{-d-1}{n}`。従って最上次数についても
$$`\dim_k H^n(X,\mathcal O(d))=\begin{cases}\binom{-d-1}{n}&d\leq-n-1,\\0&d>-n-1\end{cases}`
と計算できる。以上の三つの場合から定理が従う。証明終。

$`n=0` の場合は別に扱う。$`X=\operatorname{Spec}k` で全ての捻り線束が自明なので、
任意の整数 $`d` に対して $`H^0(X,\mathcal O(d))\cong k`、高次コホモロジーは零である。
特に負捻りの $`H^0` の消滅は $`n\geq1` の主張である。

# Ext の計算

局所自由層の Hom–cohomology 比較により
$$`\operatorname{Ext}^q_X(\mathcal O(i),\mathcal O(j))\cong H^q(X,\mathcal O(j-i)).`
$`0\leq i,j\leq n` とすれば $`-n\leq j-i\leq n` なので $`q>0` の Ext は消滅する。
負次数 $`q<0` の導来 Hom は、両対象が標準 t-structure の heart に属することから零である。
また $`i>j` のとき $`j-i<0` だから $`\operatorname{Hom}(\mathcal O(i),\mathcal O(j))=0` である。

形式化では、標準被覆の Čech 複体、単項式分解、非輪状性、Ext とコホモロジーの比較を分離する。
