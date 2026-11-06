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

# 右加群と逆向きの矢

$`A` を上の4次元 Kronecker 代数とし、頂点の冪等元を $`e_0,e_1`、
二本の矢を $`\alpha_0,\alpha_1\in e_1Ae_0` とする。
右 $`A`-加群 $`M` に対して $`M_i=Me_i=\{m\in M:me_i=m\}` とおく。
$`e_0+e_1=1` と直交性から
$$`M\xrightarrow{\sim}M_0\oplus M_1,\qquad m\longmapsto(me_0,me_1)`
は線形同型であり、逆写像は $`(u,v)\mapsto u+v` である。
右からの矢の作用は $`f_i:M_1\to M_0,\ v\mapsto v\alpha_i` を与える。
実際、$`(v\alpha_i)e_0=v(\alpha_ie_0)=v\alpha_i`。
このため、通常の箙の $`0\to1` とは *逆向き* に写像が現れる。

逆に、任意の二本の線形写像 $`f_0,f_1:V_1\to V_0` から
$`V_0\oplus V_1` 上の右作用を
$$`(u,v)\cdot(ae_0+be_1+x\alpha_0+y\alpha_1)
=(au+xf_0(v)+yf_1(v),bv)`
で定める。矢同士の積が零であることと頂点の積の規則から、これは単位的な結合的右作用である。
元の右加群から取り出した $`f_i` を使うと、上の分解同型は作用を保ち、元の加群を復元する。
有限次元の場合は $`\dim_k M=\dim_k M_0+\dim_k M_1` となる。

また頂点ごとの線形写像 $`u_0:V_0\to W_0`、$`u_1:V_1\to W_1` の直和が
右加群の射であるための必要十分条件は、二本の矢について
$$`u_0\circ f_i=g_i\circ u_1\quad(i=0,1)`
となることである。必要性は矢の作用を保つことから、十分性は上の作用公式から従う。
任意の右加群の射も頂点の冪等元の作用を保つので、必ずこの形に分解される。
これらの構成と作用の復元、射の可換条件は `Beilinson/KroneckerModule.lean` で Lean 検証した。
これらの構成は対象だけでなく射の恒等と合成も保つので関手を定める。
加群側の $`m\mapsto(me_0,me_1)` と、表現側の復元した頂点空間から元の空間への射影は、
ともに射と可換な同型である。従って右 $`A`-加群圏と逆向きの Kronecker 表現圏は圏同値となる。
上の次元公式により、これは有限次元対象の充満部分圏にも制限される。
二本の関手、両方向の自然同型、全体と有限次元部分圏の圏同値は
`Beilinson/KroneckerCategory.lean` の `moduleEquivalence` と `finiteModuleEquivalence` で Lean 検証した。
幾何学的自己準同型代数との同定と Beilinson の導来同値は依然として別の課題である。

# 射影平面

$`n=2` では頂点 $`0,1,2` の隣接頂点の間にそれぞれ三本の矢がある。
$`0\to2` の九本の長さ2の道は交換関係で六次元空間 $`\operatorname{Sym}^2(k^3)` に縮約される。
従って $`\dim_k A_2=3+3+3+6=15`。

# 検算

$`n=0` では $`A_0=k`。$`n=1` では $`\dim A_1=4`。これらの例を Lean 実装の単体テストの起点とする。
