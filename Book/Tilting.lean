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
自己 Ext の消滅により dg algebra $`B` の cohomology は次数0だけにあり、適切な truncation を通して $`B` は通常の代数 $`H^0(B)=A` と quasi-isomorphic である。
従って $`\operatorname{Perf}(B)\simeq\operatorname{Perf}(A)`。証明終。

**注意。** 上記の証明は dg Morita theorem を引用している。Lean による形式化でこの定理自体が既に検証済みとは主張していない。

# Perfect と bounded derived の比較

**補題。** ここでの $`A` は有限次元で有限大域次元を持つ。

**証明。** Properness から $`\operatorname{End}_X(T)` は有限次元。
smooth scheme の perfect dg category は smooth であり、smoothness は dg Morita 不変だから $`A` は $`A^e` 上 perfect である。
このとき $`A` の有限次元加群は有限の射影次元を持つ。実際、$`A` の有限長の $`A^e`-projective resolution を任意の有限次元右加群 $`M` と左から tensor すると、$`M` の有限長の右 $`A`-projective resolution を得る。
従って $`A` は有限大域次元を持つ。証明終。

この比較では smoothness、Morita 不変性、有限次元代数に関する homological algebra が外部依存定理である。
有限大域次元性から $`\operatorname{Perf}(A)=D^b(\operatorname{mod}_{\mathrm{fd}}A)`。また $`X` が smooth なので $`\operatorname{Perf}(X)=D^b(\operatorname{Coh}X)`。

# 主定理の証明

第4章により $`T=\bigoplus_{i=0}^n\mathcal O(i)` は tilting。
従って本章の tilting–dg Morita 定理と有限大域次元性から
$$`D^b(\operatorname{Coh}\mathbb P(V))\simeq D^b(\operatorname{mod}_{\mathrm{fd}}A_n).`
第5章により $`A_n` は関係式付き Beilinson 箙代数である。これで主定理が示された。証明終。
