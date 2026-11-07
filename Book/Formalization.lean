import VersoManual
open Verso.Genre Manual
#doc (Manual) "第8章 形式化の設計と現在の状態" =>

# 状態

本書の幾何学的な主定理について、始域・終域・関手まで一致する *Lean の証明は未完成* である。
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


# Stacks の生成性を再利用する検証

本番とは別の Lake project で、上流 revision を固定して実際の import と kernel check を行った。
次の八つは検証済みである。

1. `StacksProbe`：有限例外列、有限 total Hom、右直交の零検出からの充満性。
2. `StacksGeometryProbe`：多項式 Proj 上の座標 Koszul 複体の全次数での完全性。
3. `StacksGenerationProbe`：有限個の非正捻り線束の直和から全負捻りを生成し、その直和への直交性を全負捻りへ伝播する補題。
4. `StacksOrdinaryProbe`：非可換な degree-zero dg 代数の右加群の導来圏と、通常の反対環の加群の導来圏の三角同値。
5. `StacksAlgebraProbe`：多項式の斉次成分から作る行列 Beilinson 代数の右加群の導来圏で、compactness と有限 total cohomology の同値。
6. `DGAComparison`：基礎環上の代数同型と、次数0への集中・微分の消滅から、対応する degree-zero dg 代数との厳密な同型を構成する adapter。
7. `DegreeZeroConeComparison`：上流の二つの三角の規約の差を sign twist で補正し、幾何学側が使う cone 規約でも通常右加群への比較が三角を保つこと。
8. `ConcentratedDGA`：同じ基礎代数を保つときの degree-zero モデルとの等式を証明し、集中 dg 代数の導来圏を通常の右加群の導来圏へ比較する。両方向の exactness を確認した。

これらの宣言の依存公理は、標準の proposition extensionality、choice、quotient soundness の範囲にある。
上流の対象モジュールは StacksFrontier に属し、上流での人間レビューは未完了である。
kernel check と数学的な定式化の照合は、このレビュー状態を変更しない。

ここでの有限直和は $`E=\mathcal O\oplus\mathcal O(-1)\oplus\cdots\oplus\mathcal O(-n)`。
本書の $`T` とは $`E\otimes\mathcal O(n)` の直和成分を逆順に並べることで対応する。
多項式行列モデルと幾何学的 End の同定は、この compactness 判定とは別の課題である。
この自然同型と自己準同型代数の移送、幾何学的な右直交零検出、
通常の右加群への比較と有界連接部分圏への制限は、なお接続する必要がある。
正確な上流宣言と追加の検証ターゲットは、リポジトリの再利用台帳を参照する。
