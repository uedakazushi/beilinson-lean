import VersoManual
open Verso.Genre Manual
#doc (Manual) "第3章 対角線の Koszul 分解" =>

# 正則切断

tautological exact sequence を
$$`0\longrightarrow\mathcal O_X(-1)\longrightarrow V\otimes\mathcal O_X\longrightarrow Q\longrightarrow0`
と書く。$`Q` は階数 $`n` のベクトル束で、$`Q^\vee\simeq\Omega_X^1(1)`（Euler 列）である。
$`X\times X` 上の
$$`E=p_1^*\mathcal O_X(1)\otimes p_2^*Q`
の切断 $`s` を、第一因子の tautological line から $`V` を経由して第二因子の $`Q` へ送る写像として定める。
点 $`(\ell_1,\ell_2)` で $`s=0` となるのは $`\ell_1\subseteq\ell_2`、すなわち二つの直線が等しい場合である。
局所座標で写像の成分が対角線を生成するので、零点スキームは対角線 $`\Delta` に等しい。
その余次元は $`n=\operatorname{rank}E` であり、切断は正則である。

# 分解定理

**定理（対角線の分解）。**
$$`0\to\mathcal O(-n)\boxtimes\Omega_X^n(n)\to\cdots\to\mathcal O(-1)\boxtimes\Omega_X^1(1)\to\mathcal O\boxtimes\mathcal O\to\mathcal O_\Delta\to0`
は完全列である。

**証明。** 正則切断の Koszul complex は $`\mathcal O_\Delta` の局所自由分解を与える。さらに
$$`\bigwedge^r E^\vee\simeq p_1^*\mathcal O(-r)\otimes p_2^*(\bigwedge^rQ^\vee)\simeq\mathcal O(-r)\boxtimes\Omega_X^r(r).`
従って Koszul complex は表示された列となる。証明終。

# 生成性

**定理。** $`\mathcal O,\mathcal O(1),\ldots,\mathcal O(n)` は $`D^b(\operatorname{Coh}X)` を thick に生成する。

**証明。** 対角線の核による Fourier–Mukai 関手は恒等関手である：
$$`F\simeq\mathbf Rp_{1*}(\mathcal O_\Delta\otimes^{\mathbf L}p_2^*F).`
上記分解を tensor し pushforward すると、$`F` は
$$`\mathcal O(-r)\otimes_k^{\mathbf L}\mathbf R\Gamma(X,\Omega^r(r)\otimes^{\mathbf L}F),\quad 0\leq r\leq n`
を項とする有限複体から構成される。$`X` は proper なので係数は有限次元の有界複体である。
故に $`F` は $`\mathcal O(-n),\ldots,\mathcal O` が生成する thick 部分圏に入る。
自己同値 $`-\otimes\mathcal O(n)` を施すと主張が従う。証明終。

ここで用いるのは有限な cone と direct summand による thick 生成性であり、無限直和を許す localizing 生成性とは区別する。
