import VersoManual
open Verso.Genre Manual
#doc (Manual) "第8章 形式化の設計と現在の状態" =>

# 状態

本書の主定理と同じ始域・終域を持つ *三角同値を Lean で構成した*。
全ての次元について、実際の有限次元右 End(T) 加群の有界導来圏と、実際の有界連接導来圏を結び、両方向のシフトと三角保存を確認した。

$$`D^b(\mathrm{mod}_{\mathrm{fd}}\operatorname{End}(T))\simeq D^b(\operatorname{Coh}\mathbf P^n_k)`

ここで $`T=\mathcal O\oplus\mathcal O(1)\oplus\cdots\oplus\mathcal O(n)` は実際の正の窓である。
基礎体は Lean の `Type 0` に置く。行列代数との基礎体上の代数同型で有限次元加群の始域を移し、負の窓の同値に実際の有界導来捻りを合成する。
$`E(n)\simeq T` は実際の $`D^b(\operatorname{Coh}\mathbf P^n)` 内でも確認した。
Hom の基底は選ばない。ただし、別途古典的に定義した RHom・導来 tensor 関手との明示的な自然同型は *未検証* であり、関手の同定まで含む完成とは区別する。
Verso のビルドは文書の構文と Lean コード例を確認するが、数学の自然言語部分を証明するものではない。

# 実装の依存グラフ

1. 射影空間の Proj、線束、Euler 列。
2. Čech cohomology と線束の消滅。
3. 基点を持たない $`n+1` 個の一次形式の Koszul 完全列、任意の負捻り線束を作る帰納法。
4. Serre vanishing と大域生成性、hypercohomology spectral sequence による負捻り線束の検出、right orthogonal の消滅、exceptional collection の admissibility と SOD。
5. full strong exceptional collection の定式化。
6. Beilinson 箙の関係式付き経路代数。
7. Tilting bundle の導来 Hom–tensor 随伴と finite global dimension。dg モデルの再利用では通常右加群への比較も確認する。
8. 導来同値の主定理。

# 検証済みの代数的モデル

`Beilinson/Kronecker.lean` は $`n=1` の代数的モデルを
$$`\left\{\begin{pmatrix}a&0&0\\x&b&0\\y&0&b\end{pmatrix}:a,b,x,y\in k\right\}\subseteq M_3(k)`
として構成する。mathlib の行列・部分代数・線形同型・基底を再利用し、
$`k^4` との線形同型、次元4、二頂点の直交冪等元、二本の矢の全ての積を証明した。
積は後から通る道を左から掛ける規約であり、$`e_1\alpha=\alpha=\alpha e_0`、
$`e_0\alpha=\alpha e_1=0`、任意の二本の矢の積は零である。

これは幾何学的な $`\operatorname{End}(\mathcal O\oplus\mathcal O(1))` との同定や、
一般の経路代数構成との同型、幾何学的な導来同値をまだ含まない。

# 右加群の分解と復元

`Beilinson/KroneckerModule.lean` は右作用を反対代数から線形自己準同型代数への
$`k`-代数準同型として扱う。mathlib の `Algebra.lsmul` と `Module.compHom` により
通常の加群構造との接続も用意する。

`ofArrows` は二本の線形写像 $`V_1\to V_0` から右作用を構成する。
`arrowMap` と `decompose` は任意の右作用から逆向きの矢と二頂点空間への線形同型を取り出す。
`decompose_action` はその同型の下で元の作用が復元されることを証明する。
`prodMap_intertwines_iff` は頂点ごとの写像が加群の射となる条件を二本の矢の可換条件と同定し、
`vertexMap_arrow` と `decompose_intertwiner` は任意の加群の射がこの形で表されることを保証する。
有限次元の場合の次元の加法性も `finrank_vertices` で確認した。

# 圏同値と有限次元部分圏

`Beilinson/KroneckerCategory.lean` は `ReverseRep` を、二つのベクトル空間と
二本の $`V_1\to V_0` の写像、およびそれらと可換な頂点ごとの射の圏として定義する。
`toReverseRep` と `fromReverseRep` は mathlib の `ModuleCat` とこの表現圏の間の関手である。
`moduleUnitIso` は加群の頂点分解を自然同型にまとめる。

`representationCounitIso` は元の頂点空間の復元を自然同型にまとめる。
これらから `moduleEquivalence` は
$$`\operatorname{Mod}\text{-}A\simeq\operatorname{Rep}_k(K_2^{\mathrm{op}})`
を mathlib の圏同値の構造体として与える。
ここで始域は反対代数の左加群圏であり、$`k` の作用は代数準同型からの制限である。

`finite_toReverseRep_iff` は有限次元性が両頂点空間の有限次元性と同値であることを示し、
`finiteModuleEquivalence` は有限次元対象の充満部分圏の間の圏同値を与える。
これはあくまで具体的な代数モデルの加群圏同値であり、射影直線上の層の圏や導来圏との同値ではない。

# 射影分解と射影次元

`Beilinson/KroneckerResolution.lean`

このファイルは表現の全射性を頂点ごとの全射性と同定し、二種類の標準表現の射影性を持ち上げ性により証明する。
主要な宣言は次の通りである。

1. `standardResolution`：二本の矢の関係を用いた標準分解。
2. `rightModuleResolution`：任意の右加群を終点とする加群圏の短複体。
3. `rightModuleResolution_shortExact`：短完全性。両項の射影性と合わせて長さ1の射影分解を与える。
4. `finite_rightModuleResolution_terms`：有限次元の右加群の分解は両項とも有限次元となる。
5. `rightModule_projectiveDimension_le_one`：mathlib の射影次元に関して、全ての右加群 $`M` で $`\operatorname{pd}_A M\leq1`。

一般次元の Beilinson 代数の有限大域次元性や、幾何学的な tilting theorem はまだ含まない。

# 上界の鋭さ

`Beilinson/KroneckerDimension.lean`

このファイルは頂点1だけに1次元空間を持つ表現から右加群を構成する。

1. `sourceSimpleModule_simple`：全ての非零ベクトルが全体を生成するという既存の判定法による単純性。
2. `sourceSimpleModule_not_projective`：標準射影全射に切断があれば矢との可換性に反することによる非射影性。
3. `sourceSimpleModule_projectiveDimension`：射影次元がちょうど1となること。
4. `sourceSimpleModule_finite`：この例は基礎体上有限次元であること。

# 頂点右イデアル

`Beilinson/KroneckerIdeals.lean`

1. `mem_fixedLeft_iff`：冪等元の左乗法で固定される部分加群は、その冪等元が生成する右イデアルと一致する。
2. `sinkIdealEquiv`：sink 表現の右加群と $`e_0A` の同型。
3. `sourceIdealEquiv`：二本の包含写像を持つ source 射影表現の右加群と $`e_1A` の同型。
4. `vertexIdealDecomposition`：正則右加群 $`A` を $`e_0A\oplus e_1A` に分解する同型。

両右イデアルについて、圏論的な射影性と通常の加群としての射影性の両方を確認した。
次は既存の射影空間・線束・コホモロジーの API を照合し、幾何学側への接続を進める。
証明済み Lean 宣言、外部の既知数学定理、自然言語の証明、未実装の仕様を常に区別する。


# 二対象の直和の自己準同型代数

`Beilinson/KroneckerEnd.lean` は一般の $`k`-線形圏での計算である。
二対象 $`X,Y` の対角 Hom を $`k` と線形同定し、それぞれ恒等射を1へ送ると仮定する。
さらに $`\operatorname{Hom}(Y,X)=0` とし、$`\operatorname{Hom}(X,Y)` の二元基底を選ぶ。
このとき `algebraEquiv` は具体的 Kronecker 代数と $`\operatorname{End}(X\oplus Y)` の代数同型を与える。

`ofArrows` は、任意の二本の射 $`f_0,f_1:X\to Y` からこの直和への代数作用を作る。
頂点は $`X,Y` への射影と包含の合成へ、矢は $`f_i` を順向きの非対角成分へ置いた射へ送る。
`finrank` は、上の基底と対角 Hom の仮定の下で、End の次元が4であることを示す。

これは追加仮定を明示した一般的な End の同定であり、
射影直線上の $`X=\mathcal O`、$`Y=\mathcal O(1)` について必要な Hom データを
Lean で代入する幾何学的ステップはまだ残っている。

`Beilinson/KroneckerYoneda.lean` は $`\operatorname{Hom}(X\oplus Y,Z)` を二つの Hom の積へ線形分解する。
`homCoordinates_precompose` は End の前合成作用が、$`f_i` との合成による逆向きの
二本の線形写像から作った右 Kronecker 作用と一致することを示す。
さらに `homFunctorIso` は、mathlib の標準の右 End 作用を制限した Hom 関手と、
二つの Hom を頂点に持つ表現から構成した右加群関手の自然同型を与える。
作用の式だけでなく、通常の加群とその射のレベルでも本文の矢の規約を照合できる。

`Beilinson/KroneckerEndModules.lean` は反対環の環同型に沿って短完全列と
射影性を移送し、最後の項を元の加群と同型で結ぶ。
したがって上の Hom の仮定の下では、$`\operatorname{End}(X\oplus Y)` のすべての
右加群の射影次元も高々1である。独立ターゲット `ProjectiveLineEnd` で、実際の射影直線の O(0), O(1) に Hom データを代入する計算も検証した。

# 有限次元加群の部分圏

`Beilinson/KroneckerFinite.lean` は有限次元右加群が部分対象・商・拡大で閉じる Serre 部分圏であることを示す。
有限次元対象への任意の全射に対し、既存の有限射影被覆を射影性によって持ち上げることで、
有限次元対象からの射で、元の全射との合成が再び全射となるものを構成する。
この被覆条件を独立ターゲット `KroneckerBoundedDerived` の導来包含の比較に用いる。

# 有界対象のコホモロジーからの再構成

`Beilinson/DerivedDevissage.lean` は任意のアーベル圏 $`C` と、その導来圏の
同型で閉じた三角部分圏 $`P` を扱う。
`of_bounded_cohomology` は、コホモロジーが有限区間に支持される対象 $`K` について、
全ての $`H^i(K)[0]` が $`P` に入れば $`K` も $`P` に入ることを示す。
`of_isBounded` は上下界を存在命題として受け取る形である。

証明は最上次数のコホモロジーを標準の truncation 三角で分離し、区間の長さを帰納する。
射影分解や環の可換性は仮定しない。
非可換な自己準同型代数の加群について、各コホモロジー加群から複体全体の
perfect 性へ進む際に使える。ただし、この一般補題だけで各加群の perfect 性が得られるわけではない。

`Beilinson/KroneckerPerfect.lean` は、Kronecker 加群の検証済みの短完全な射影分解を
mathlib の `singleTriangle` で導来圏の三角へ送る。
その両項が有限次元かつ射影であることから、有限次元加群を含むためには
有限射影加群を含めば十分である。さらに上の一般補題により、有界かつコホモロジーが
有限次元の複体も、有限射影加群を含む任意の厳密充満な三角部分圏に入る。
この一般的な所属条件への compact / perfect の具体的代入は、下の独立した Stacks ターゲットで検証した。

# Stacks の生成性を再利用する検証

本番とは別の Lake project で、上流 revision を固定して実際の import と kernel check を行った。
次の四十八個は検証済みである。

1. `StacksProbe`：有限例外列、有限 total Hom、右直交の零検出からの充満性。
2. `StacksGeometryProbe`：多項式 Proj 上の座標 Koszul 複体の全次数での完全性。
3. `StacksGenerationProbe`：有限個の非正捻り線束の直和から全負捻りを生成し、その直和への直交性を全負捻りへ伝播する補題。
4. `StacksOrdinaryProbe`：非可換な degree-zero dg 代数の右加群の導来圏と、通常の反対環の加群の導来圏の三角同値。
5. `StacksAlgebraProbe`：多項式の斉次成分から作る行列 Beilinson 代数の右加群の導来圏で、compactness と有限 total cohomology の同値。
6. `DGAComparison`：基礎環上の代数同型と、次数0への集中・微分の消滅から、対応する degree-zero dg 代数との厳密な同型を構成する adapter。
7. `DegreeZeroConeComparison`：上流の二つの三角の規約の差を sign twist で補正し、幾何学側が使う cone 規約でも通常右加群への比較が三角を保つこと。
8. `ConcentratedDGA`：同じ基礎代数を保つときの degree-zero モデルとの等式を証明し、集中 dg 代数の導来圏を通常の右加群の導来圏へ比較する。両方向の exactness を確認した。

9. `GeometricPerfectProbe`：準コンパクトかつ準分離な正則スキームで、compact な $`D_{\mathrm{QCoh}}` 対象と有界 coherent コホモロジーを持つ対象の一致。
10. `ProjectivePerfectProbe`：任意の体上の多項式 Proj の正則性と、上の compactness 判定への代入。次元0も含む。

11. `KroneckerCompact`：本番の Kronecker 証明を再利用し、右加群の複体について、compactness / perfect 性と有界・有限次元コホモロジーの同値を確認する。幾何学的な End の同定は含まない。

12. `SheafHomSections`：構造層からの Hom と大域切断の線形同型、対象に関する自然性、切断とテンソルのスカラー構造の一致。

13. `ProjectiveLineEnd`：任意の体上の実際の多項式 Proj で、O(0) と O(1) の直和の End を Kronecker 代数と同定し、全右加群の射影次元≤1を導く。二次元 Hom の基底を選ぶ同型である。

14. `CoherentDerivedComparison`：Noether スキームで、$`D^b(\operatorname{Coh}X)` 自体と、小さい導来モデルの $`D_{\mathrm{QCoh}}` における有界連接部分圏との同値。シフトと三角の保存を両方向で確認する。

15. `KroneckerBoundedDerived`：有限次元右 Kronecker 加群の有界導来圏自体と、通常の右加群の導来圏の compact 部分圏との三角同値を両方向で確認する。

16. `StacksCohomologyProbe`：基底変換モデルの射影空間で、Beilinson の負捻りの帯の全ての高次順像が零となること。
17. `StacksBeilinsonProbe`：実際の非有界 dg tensor 関手の同値性・三角保存と、幾何学的 dg 代数の次数0への集中。
18. `OrdinaryBeilinson`：cone の符号を補正した通常右 End 加群への移送。現状は `Type 0` の可換基礎環を使う。
19. `BoundedBeilinson`：任意の次元で、compact な通常右 End 加群の導来部分圏と実際の有界連接導来圏を結ぶ。両方向の三角保存を確認する。
20. `ProjectiveLineWindow`：実際の負の窓の生成対象の End を Kronecker 代数と同定し、正の窓の End とも比較する。基底選択を用いる代数同型である。
21. `ProjectiveLineBeilinson`：具体的 Kronecker 代数の有限次元右加群の有界導来圏自体と、射影直線の連接層の有界導来圏自体との三角同値を合成する。

22. `PositiveWindow`：任意の可換環・全次元で、実際の E(n) と正の窓 T の同型と、捻りによる End 代数の同型を得る。Hom の基底選択を用いない。右 End(E) 加群として自然な Hom(E,M)≅Hom(T,M(n)) と、その複体上の比較も確認する。

23. `CentralDegreeZero`：集中 dg 代数の通常右加群への比較が、追加の中心的な係数環について両方向とも線形となること。
24. `OrdinaryBeilinsonLinear`：実際の通常右加群からの Beilinson tensor 関手が、幾何学的基礎環上で線形となること。

25. `MatrixAlgebraComparison`：compactness 判定の行列代数と幾何側の行列代数が同じ部分代数であることと、有限次元性。
26. `FiniteBoundedDerived`：任意の有限次元代数について、有限次元加群の有界導来圏と、通常の導来圏の有限次元コホモロジー部分圏を三角同値で結ぶ。
27. `GeometricMatrixEnd`：全次元で行列代数を実際の負の窓の End と環同型で同定する。
28. `MatrixBeilinson`：全次元で、有限次元右 Beilinson 行列代数加群の有界導来圏自体と、実際の有界連接導来圏自体との三角同値を得る。

29. `CoherentTensor`：可逆層とのテンソルは、実際の連接層の圏の同値を与える。
30. `ExactBoundedEquivalence`：アーベル圏の完全な同値から、選択した導来モデル上の実際の有界導来圏の三角同値を得る。
31. `CoherentTensorBounded`：可逆層との実際の有界導来 tensor 同値と、次数0に置いた連接層での値。
32. `PositiveBounded`：全次元の有界導来捻り、実際の有界連接導来圏内の E(n)≅T、および負の窓の同値との合成。
33. `GeometricMatrixLinear`：幾何学的行列–End 同型の基礎体上のスカラー保存と、正負両窓の End との代数同型。
34. `FiniteScalarEquivalence`：代数同型に沿う有限次元加群の実際の圏と、その有界導来圏の三角比較。
35. `PositiveEndBounded`：実際の有限次元右 End(T) 加群の有界導来圏自体と、実際の有界連接導来圏自体との全次元の三角同値。
36. `TensorDerivedModels`：全加群の選択した導来モデル上の捻りと連接層の導来捻りが、導来包含を通して自然に対応すること。
37. `ExactFunctorModels`：完全関手の導来化と、終域の導来圏モデルの変更を比較する自然同型。
38. `DerivedHomTransport`：通常の右 End 加群に値を持つ Hom の全右導来関手の存在と、完全同値・係数変更との自然な対応。
39. `PositiveDerivedHom`：全次元で、別に定義した古典的 RHom(E,−) と RHom(T,−) を捻りと係数変更を通して自然に同型にする。
40. `GeometricHomEvaluation`：実際の幾何学的 dg Hom の各斉次成分を通常の Hom と同定し、微分・右 End 作用・後合成の対応を確認する。
41. `ConcentratedComponents`：次数0に集中する dg 代数上の加群から、斉次成分の通常の加群複体を直接構成する。
42. `GeometricHomComplex`：実際の dg Hom の成分複体と、通常の右加群 Hom の項別適用を関手として自然に同型にする。
43. `ConcentratedComparisonComponents`：既存の通常加群への導来比較そのものが、成分複体の局所化として計算できること。
44. `GeometricDerivedHom`：実際の幾何学的 dg RHom を通常加群へ移した関手と、独立に導来化した古典的 RHom の自然同型。
45. `RingChangeDerived`：実際の通常加群の導来圏で、連続する環変更を自然同型によって打ち消す。
46. `DerivedFunctorModels`：局所化のモデル変更と、全右導来関手の自然な対応。
47. `GeometricEndHom`：古典的 RHom の終域を実際の右 End(E) 加群として記述し、幾何学的 dg RHom と比較する。
48. `DerivedEquivalenceModels`：源の二つの導来モデルを明示して、完全同値を通した古典的導来関手の比較を与える。

本番の `AdjunctionLift` は随伴の終域を充満部分圏へ制限し、指定された右随伴と同値の逆関手を比較する。
`EndRingYoneda` は指定された End 環同型に沿う通常の右加群 Hom の自然同型を与え、
`EquivalenceSquare.inverse` は同値の前向き関手の可換な比較を逆関手へ移す。

本番の `CochainFromZero.functorIso` は、次数0に集中する複体からの Hom 複体と
通常の Hom を各項へ適用した複体を自然に同型にする。
微分、写像による後合成、次数0の自己準同型による前合成の対応も検証した。

これらの宣言の依存公理は、標準の proposition extensionality、choice、quotient soundness の範囲にある。
上流の対象モジュールは StacksFrontier に属し、上流での人間レビューは未完了である。
kernel check と数学的な定式化の照合は、このレビュー状態を変更しない。

ここでの有限直和は $`E=\mathcal O\oplus\mathcal O(-1)\oplus\cdots\oplus\mathcal O(-n)`。
本書の $`T` とは $`E\otimes\mathcal O(n)` の直和成分を逆順に並べることで対応する。
対象・End・Hom と複体の移送に加え、実際の有界導来捻りとの合成と正の End(T) の始域を確認した。別定義の古典的 RHom・導来 tensor 関手全体との自然同型が残る。
