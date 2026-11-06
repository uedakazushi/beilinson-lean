import VersoManual
open Verso.Genre Manual
#doc (Manual) "第7章 低次元の具体例" =>

# 射影直線と Kronecker 箙

$`n=1` とすると $`T=\mathcal O\oplus\mathcal O(1)` である。
二頂点 $`0,1` と二本の平行矢 $`0\to1` からなる Kronecker 箙の経路代数を $`K_2` とすると
$$`D^b(\operatorname{Coh}\mathbb P^1)\simeq D^b(\operatorname{mod}_{\mathrm{fd}}kK_2).`
ここでは長さ2の道がないので追加関係式はない。
対角線分解は
$$`0\to\mathcal O(-1)\boxtimes\mathcal O(-1)\to\mathcal O\boxtimes\mathcal O\to\mathcal O_\Delta\to0`
となる。$`\Omega_{\mathbb P^1}^1(1)\simeq\mathcal O(-1)` を用いた。

# 射影平面

$`n=2` では頂点 $`0,1,2` の隣接頂点の間にそれぞれ三本の矢がある。
$`0\to2` の九本の長さ2の道は交換関係で六次元空間 $`\operatorname{Sym}^2(k^3)` に縮約される。
従って $`\dim_k A_2=3+3+3+6=15`。

# 検算

$`n=0` では $`A_0=k`。$`n=1` では $`\dim A_1=4`。これらの例を Lean 実装の単体テストの起点とする。
