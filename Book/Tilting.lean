import VersoManual
open Verso.Genre Manual
#doc (Manual) "第6章 Tilting と導来同値" =>

# Tilting bundle の導来 Hom–tensor 随伴

$`\operatorname{Perf}(X)` は、局所的に有界な有限階数局所自由層の複体で表される対象の充満部分圏である。
環 $`A` に対して $`\operatorname{Perf}(A)` は、有界な有限生成射影右 $`A`-加群の複体で表される対象の充満部分圏をいう。
いずれも shift、cone、直和因子で閉じている。

**定理。** $`X` を体上の smooth proper scheme とし、$`T` をベクトル束とする。
$`\operatorname{Ext}^q_X(T,T)=0`（$`q\neq0`）および
$`\operatorname{thick}\langle T\rangle=\operatorname{Perf}(X)` と仮定する。
$`A=\operatorname{End}_X(T)` とおくと
$$`G=\mathbf R\operatorname{Hom}_X(T,-):\operatorname{Perf}(X)\xrightarrow{\sim}\operatorname{Perf}(A)`
は三角圏同値である。

**証明。** まず関手と随伴を構成する。$`A` は $`T` に左から作用する。
有限生成射影右 $`A`-加群 $`P` は $`A^r` の直和因子なので、$`P\otimes_A T` も
$`T^r` の直和因子であり、ベクトル束となる。
有界な有限生成射影加群の複体へ項ごとに tensor を適用し、
$$`L(P)=P\otimes_A^{\mathbf L}T`
を定める。有界な射影複体の間の quasi-isomorphism は homotopy equivalence であり、
tensor は homotopy を保つから、これは $`\operatorname{Perf}(A)` 上の関手を定める。
ここでは、有界射影複体を始域とする導来圏の射が chain map の homotopy 類で計算できることを用いている。
shift と cone に可換なので三角関手であり、$`L(A)\cong T` である。

一方、$`F` の層の単射分解 $`I^\bullet` を取り、
$$`G(F)=\operatorname{Hom}^\bullet_X(T,I^\bullet)`
とする。ここでの単射分解は全ての $`\mathcal O_X`-加群の圏で取り、
各項の Hom には $`A` の前合成による右作用を入れる。
導来関手の構成により、初めは $`G:\operatorname{Perf}(X)\to D(\operatorname{Mod}\text{-}A)` を得る。
有界射影複体 $`P` と単射分解 $`I^\bullet` の間の複体レベルの tensor–Hom 随伴から、
自然な同型
$$`\operatorname{Hom}(L(P),F)\cong\operatorname{Hom}(P,G(F))`
を得る。従って $`L` と $`G` は導来圏上でも随伴し、両者は三角関手である。

自己 Ext の仮定から $`G(T)` のコホモロジーは次数0の $`A` だけである。
随伴の単位 $`\eta_A:A\to G(L(A))` は、この次数0で恒等写像を与えるため同型となる。
また $`G` は三角と直和因子を保ち、$`G(T)\cong A` であるから、
$$`G(\operatorname{thick}\langle T\rangle)\subseteq\operatorname{thick}\langle A\rangle=\operatorname{Perf}(A).`
従って $`G` は実際に定理の終域へ値を持ち、上の随伴を二つの Perf 圏に制限できる。

単位 $`\eta_P:P\to G(L(P))` が同型となる対象のなす部分圏は thick である。
これは shift と有限直和との可換性、三角のうち二つが同型なら残りも同型となること、
および直和因子への制限から分かる。その部分圏は $`A` を含むので、$`\operatorname{Perf}(A)` 全体である。
余単位 $`\epsilon_{L(A)}` については、随伴の三角恒等式
$$`\epsilon_{L(A)}\circ L(\eta_A)=1_{L(A)}`
により同型である。余単位が同型となる対象のなす部分圏も thick であり、
$`L(A)\cong T` を含むから、仮定より $`\operatorname{Perf}(X)` 全体となる。
従って単位と余単位が全対象で同型となり、$`L` と $`G` は互いに逆な三角圏同値を与える。証明終。

この議論は $`T` のベクトル束としての厳密な左 $`A`-作用と、通常の導来 Hom–tensor 随伴を用いる。
本章の自然言語の関手を、始域・終域・作用まで一致させた Lean の証明へ接続する作業は継続中である。

# dg モデルによる補足

一般の perfect complex を $`T` とする拡張では、dg 自己準同型代数
$`B=\mathbf R\operatorname{End}_X(T)` を使う方法がある。
dg 増強と導来 Morita theorem により $`\operatorname{Perf}(X)\simeq\operatorname{Perf}(B)` を得る。
自己 Ext の消滅により $`B` の cohomology が次数0だけであるとき、
乗法を保つ truncation $`\tau_{\leq0}B` を、負次数では $`B` と同じ、
次数0では $`\ker(d:B^0\to B^1)`、正次数では零として作る。
次数0の cocycle をその cohomology class へ送り、負次数を零へ送ることで、dg algebra の射の列
$$`B\longleftarrow\tau_{\leq0}B\longrightarrow H^0(B)=A`
を得る。両射は全ての次数で cohomology 同型なので quasi-isomorphism である。
従って $`\operatorname{Perf}(B)\simeq\operatorname{Perf}(A)` となる。

この一般化では dg Morita theorem を外部定理として使う。
形式化でも dg モデルと通常の右加群の比較が必要であり、
第8章の検証状況は、この比較と本書の主定理の完成を区別して記録している。

# Perfect と bounded derived の比較

**補題。** Beilinson 代数 $`A_n` は有限次元であり、全ての右加群の射影次元は高々 $`n` である。

**証明。** 有限次元性は第5章の Hom の計算による。
同章の頂点冪等元を $`e_0,\ldots,e_n` とすると、
$$`e_jA_ne_i=0\quad(j<i),\qquad e_iA_ne_i=k e_i.`
非対角成分の和 $`J` は両側イデアルで、$`J^{n+1}=0`、
$`A_n/J\cong k^{n+1}` である。従って $`J` は Jacobson radical。
頂点 $`i` に対応する単純右加群を $`S_i=e_iA_n/e_iJ` とおく。

射影右加群 $`P_i=e_iA_n` は、頂点 $`0,\ldots,i` にのみ成分を持つ。
その radical $`e_iJ` の組成因子は $`S_0,\ldots,S_{i-1}` に限られる。
$`P_0=S_0` は射影である。帰納的に $`\operatorname{pd}S_j\leq j`（$`j<i`）とすれば、
有限組成列に沿う短完全列の射影次元不等式から $`\operatorname{pd}(e_iJ)\leq i-1`。
短完全列
$$`0\longrightarrow e_iJ\longrightarrow P_i\longrightarrow S_i\longrightarrow0`
により $`\operatorname{pd}S_i\leq i` となる。

この上界は有限次元加群に限らない。任意の右加群 $`M` に対して
$$`F_iM=\bigoplus_{0\leq j\leq i}Me_j,\qquad F_{-1}M=0`
とおく。右乗法は頂点番号を下げるので $`F_iM` は右部分加群である。
商 $`F_iM/F_{i-1}M` は頂点 $`i` のみに成分を持ち、$`k`-基底を選べば $`S_i` の直和となる。
$`S_i` の長さ高々 $`i` の射影分解を直和することで、この商も射影次元高々 $`i`。
有限列 $`0=F_{-1}M\subseteq F_0M\subseteq\cdots\subseteq F_nM=M` に沿って
短完全列の射影次元不等式を使うと $`\operatorname{pd}M\leq n` である。証明終。

この証明は幾何学的 dg category の smoothness の Morita 不変性を必要とせず、
第5章の代数の三角形状と通常の加群の homological algebra から上界を与える。
有限次元代数上の有限次元加群の有限射影分解は有限生成射影加群で選べるので、
$$`\operatorname{Perf}(A_n)=D^b(\operatorname{mod}_{\mathrm{fd}}A_n).`
一方、$`X=\mathbb P(V)` は正則な有限次元 noetherian scheme であり、
全ての連接層は有限長の局所自由分解を持つ。従って
$`\operatorname{Perf}(X)=D^b(\operatorname{Coh}X)`。
この最後の比較では、$`D^b(\operatorname{Coh}X)` の層の導来圏への標準埋め込みと
bounded coherent cohomology による記述を用いている。

# 主定理の証明

第4章により $`T=\bigoplus_{i=0}^n\mathcal O(i)` は tilting。
従って本章の tilting bundle の定理と有限大域次元性から
$$`D^b(\operatorname{Coh}\mathbb P(V))\simeq D^b(\operatorname{mod}_{\mathrm{fd}}A_n).`
第5章により $`A_n` は関係式付き Beilinson 箙代数である。これで主定理が示された。証明終。
