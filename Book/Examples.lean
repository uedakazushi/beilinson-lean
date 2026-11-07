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
これらの構成と作用の復元、射の可換条件は次のファイルで Lean 検証した。

`Beilinson/KroneckerModule.lean`

これらの構成は対象だけでなく射の恒等と合成も保つので関手を定める。
加群側の $`m\mapsto(me_0,me_1)` と、表現側の復元した頂点空間から元の空間への射影は、
ともに射と可換な同型である。従って右 $`A`-加群圏と逆向きの Kronecker 表現圏は圏同値となる。
上の次元公式により、これは有限次元対象の充満部分圏にも制限される。
二本の関手、両方向の自然同型、全体と有限次元部分圏の圏同値を、次のファイルで Lean 検証した。

`Beilinson/KroneckerCategory.lean`

1. `moduleEquivalence`：全ての右加群と逆向きの表現の圏同値。
2. `finiteModuleEquivalence`：有限次元対象の充満部分圏への制限。

幾何学的自己準同型代数との同定と Beilinson の導来同値は依然として別の課題である。

# Hom 関手で矢の向きを確認する

同次座標を $`x_0,x_1` とし、それらに対応する射
$`\mathcal O\to\mathcal O(1)` を選ぶ。
任意の coherent 層 $`F` に対し、$`R\operatorname{Hom}(T,F)` の第 $`q` コホモロジーの
二頂点は
$$`\bigl(H^q(F),H^q(F(-1))\bigr)`
であり、二本の逆向きの矢は
$$`x_i:H^q(F(-1))\longrightarrow H^q(F)\qquad(i=0,1)`
である。これは Hom の前合成そのものである。
$`\operatorname{Hom}(\mathcal O(1),F)` の元を $`x_i:\mathcal O\to\mathcal O(1)` と合成すると、
$`\operatorname{Hom}(\mathcal O,F)` の元を得るので、矢の向きが直接確認できる。
一般の線形圏での分解・前合成の両立性・自然性は、次のファイルで検証した。

`Beilinson/KroneckerYoneda.lean`

以下の線束・層への具体的な代入は、本書の自然言語の導来同値を使う計算である。

特に $`F=\mathcal O` は $`(k,0)` に、$`F=\mathcal O(1)` は
$`(k^2,k;v\mapsto(v,0),v\mapsto(0,v))` に移る。
従って tilting 束の二つの直和因子は、後で具体的に同定する頂点右射影 $`e_0A,e_1A` に対応する。
$`d\geq1` の $`F=\mathcal O(d)` では頂点次元が $`(d+1,d)` となり、
矢は同次多項式への $`x_0,x_1` の乗法で与えられる。

$`\mathcal O(-1)` の像は第1コホモロジーだけが $`L=(0,k;0,0)` となり、他は零である。従って
$$`R\operatorname{Hom}(T,\mathcal O(-1))\simeq L[-1],\qquad
L\longleftrightarrow\mathcal O(-1)[1].`
実際、射影直線の Euler 完全列
$$`0\longrightarrow\mathcal O(-1)\xrightarrow{(-x_1,x_0)}
\mathcal O^{\oplus2}\xrightarrow{(x_0,x_1)}\mathcal O(1)\longrightarrow0`
に $`R\operatorname{Hom}(T,-)` を適用すると、コホモロジーの完全列から
$$`0\longrightarrow(e_0A)^{\oplus2}\longrightarrow e_1A\longrightarrow L\longrightarrow0`
を得る。これは下で構成する $`L` の長さ1の射影分解を、幾何学側から説明する。

また $`k`-有理点 $`p=[s:t]` の skyscraper 層 $`k(p)` は、両頂点が $`k` で、
二本の矢がそれぞれ $`s,t` 倍となる表現に対応する。
ここではファイバーの基底を選んでいる。基底変更による共通の非零スカラー倍は表現の同型を与えるので、
$`[s:t]` という射影座標にのみ依存する。

# 長さ1の射影分解

逆向きの Kronecker 表現 $`X=(X_0,X_1;f_0,f_1)` に対し、
$`S(U)=(U,0)` および
$$`P(U,V)=(U\oplus V\oplus V,V;\ v\mapsto(0,v,0),\ v\mapsto(0,0,v))`
を定める。これらは任意のベクトル空間 $`U,V` に対して射影対象である。
実際、表現の全射は両頂点での全射と同値であり、
$`S(U)` からの射は $`U\to X_0` により、$`P(U,V)` からの射は
$`U\to X_0` と $`V\to X_1` により一意に決まる。
ベクトル空間の全射に対する線形写像の持ち上げを使えば、表現の全射に対しても持ち上げられる。

$`P_X=P(X_0,X_1)` とおき、射 $`\varepsilon:P_X\to X` を頂点ごとに
$$`\varepsilon_0(u,s,t)=u+f_0(s)+f_1(t),\qquad\varepsilon_1(v)=v`
と定める。これは全射である。核は $`S(X_1\oplus X_1)` と同型であり、包含は
$$`d_0(s,t)=(-f_0(s)-f_1(t),s,t),\qquad d_1=0`
で与えられる。従って
$$`0\longrightarrow S(X_1\oplus X_1)\xrightarrow{d}P_X\xrightarrow{\varepsilon}X\longrightarrow0`
は両項が射影的な短完全列である。$`X_0,X_1` が有限次元なら、全ての項が有限次元である。

既に構成した加群圏同値でこれを移し、終点を元の加群と同型で同定すると、
任意の右 $`A`-加群 $`M` に対して長さ1の射影分解が得られる。
従って $`\operatorname{pd}_A M\leq1` である。
`Beilinson/KroneckerResolution.lean` は標準分解を mathlib の加群圏の短完全列として構成し、
両項の射影性・有限次元性の保存・射影次元の上界まで Lean 検証する。

# 上界を達成する単純加群

頂点1にだけ $`k` を持つ表現 $`L=(0,k;0,0)` を考える。
その標準射影全射 $`P(0,k)\to L` に切断 $`s` があれば、頂点1では $`s_1=\mathrm{id}_k` となる。
しかし第一の矢との可換性は $`0=(s_1(1),0)=(1,0)` を要求し、矛盾する。
従って $`L` と対応する右加群は射影的でない。
上の普遍的な上界と合わせて、右加群としての射影次元はちょうど1となる。

この加群は有限次元かつ単純である。実際、非零のベクトル $`v` から任意のベクトル $`w` へは、
頂点1の係数を $`w/v` とした代数の元を作用させればよいので、非零ベクトルは全体を生成する。
`Beilinson/KroneckerDimension.lean` は単純性・非射影性・射影次元1を Lean 検証する。

# 頂点右イデアルと標準射影表現

冪等元 $`e` に対して、右イデアル $`eA` は
$`\{a\in A:ea=a\}` と一致する。これは左からの $`e` の乗法で固定される部分空間であり、
右 $`A`-作用で閉じている。

先の座標表示では $`e_0A` は $`ae_0` の形の元からなり、sink 表現 $`(k,0)` に対応する。
$`e_1A` は $`be_1+x\alpha_0+y\alpha_1` の形の元からなり、
二本の包含写像を持つ表現 $`(k^2,k;v\mapsto(v,0),v\mapsto(0,v))` に対応する。
従って両者は射影右加群である。

$`e_0+e_1=1` と直交性から、正則右加群の分解は
$$`A\xrightarrow{\sim}e_0A\oplus e_1A,\qquad a\longmapsto(e_0a,e_1a)`
で与えられ、逆写像は和である。
`Beilinson/KroneckerIdeals.lean` は二つの明示的な右加群同型、両右イデアルの射影性、
正則右加群の直和分解を Lean 検証する。

# 射影平面

$`n=2` では頂点 $`0,1,2` の隣接頂点の間にそれぞれ三本の矢がある。
$`0\to2` の九本の長さ2の道は交換関係で六次元空間 $`\operatorname{Sym}^2(k^3)` に縮約される。
従って $`\dim_k A_2=3+3+3+6=15`。

# 検算

$`n=0` では $`A_0=k`。$`n=1` では $`\dim A_1=4`。これらの例を Lean 実装の単体テストの起点とする。
