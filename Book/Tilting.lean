import VersoManual
open Verso.Genre Manual
#doc (Manual) "第6章 Tilting theorem と導来同値" =>

# 抽象的な定理

**定理（tilting–dg Morita）。** $`X` を体上の smooth proper scheme とし、$`T` を perfect complex とする。
$`\operatorname{Ext}^q_X(T,T)=0`（$`q\neq0`）および
$`\operatorname{thick}\langle T\rangle=\operatorname{Perf}(X)` と仮定する。
$`A=\operatorname{End}_X(T)` とおくと
$$`\mathbf R\operatorname{Hom}_X(T,-):\operatorname{Perf}(X)\xrightarrow{\sim}\operatorname{Perf}(A)`
は同値である。

**証明（標準的な dg Morita theorem を使用）。** $`D(\operatorname{QCoh}X)` の dg 増強を用い、$`B=\mathbf R\operatorname{End}_X(T)` とする。
$`T` は compact かつ perfect objects を thick に生成するため compact generator である。
導来 Morita theorem から $`\operatorname{Perf}(X)\simeq\operatorname{Perf}(B)` を得る。
自己 Ext の消滅により dg algebra $`B` の cohomology は次数0だけにある。
乗法を保つ truncation $`\tau_{\leq0}B` を、負次数では $`B` と同じ、
次数0では $`\ker(d:B^0\to B^1)`、正次数では零として作る。
次数0の cocycle をその cohomology class へ送り、負次数を零へ送ることで、dg algebra の射の列
$$`B\longleftarrow\tau_{\leq0}B\longrightarrow H^0(B)=A`
を得る。両射は全ての次数で cohomology 同型なので quasi-isomorphism である。
従って $`\operatorname{Perf}(B)\simeq\operatorname{Perf}(A)`。証明終。

**注意。** 上記の証明は dg Morita theorem を引用している。Lean による形式化でこの定理自体が既に検証済みとは主張していない。

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
従って本章の tilting–dg Morita 定理と有限大域次元性から
$$`D^b(\operatorname{Coh}\mathbb P(V))\simeq D^b(\operatorname{mod}_{\mathrm{fd}}A_n).`
第5章により $`A_n` は関係式付き Beilinson 箙代数である。これで主定理が示された。証明終。
