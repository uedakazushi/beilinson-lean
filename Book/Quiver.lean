import VersoManual
open Verso.Genre Manual
#doc (Manual) "第5章 Beilinson 箙の計算" =>

# Hom と多項式の積

$`S=\operatorname{Sym}(V^\vee)` とする。線束の cohomology の計算から
$$`\operatorname{Hom}_X(\mathcal O(i),\mathcal O(j))\cong\begin{cases}S_{j-i}&i\leq j,\\0&i>j.\end{cases}`
これらの同型の下で合成は対称代数における積に対応する。

# 関係式付き経路代数

頂点集合を $`\{0,1,\ldots,n\}` とし、隣接する頂点 $`i\to i+1` に $`V^\vee` の基底 $`x_0,\ldots,x_n` に対応する $`n+1` 本の矢を置く。
矢 $`x_a^{(i)}` に対し、全ての $`0\leq i\leq n-2`、$`a,b` について
$$`x_a^{(i+1)}x_b^{(i)}=x_b^{(i+1)}x_a^{(i)}`
という関係を課す。

**定理。** この関係式付き経路代数は $`A_n=\operatorname{End}_X(\bigoplus_{i=0}^n\mathcal O(i))` と同型である。

**証明。** 矢をそれぞれ線束間の一次形式の乗法写像に送る。多項式環の可換性から関係式が成立する。
頂点 $`i` から $`j\geq i` への長さ $`j-i` の道の商は、隣接交換で割った
$`(V^\vee)^{\otimes(j-i)}`、すなわち $`\operatorname{Sym}^{j-i}(V^\vee)` に等しい。
前節の Hom と各成分で一致するため全体でも同型である。証明終。

頂点番号が常に増えるため道の長さは高々 $`n` で、代数は有限次元：
$$`\dim_k A_n=\sum_{0\leq i\leq j\leq n}\binom{n+j-i}{n}.`

経路代数の積は「後から通る道を左から掛ける」規約。右 $`A_n`-加群と通常の左箙表現との間には反対代数の注意が必要である。
