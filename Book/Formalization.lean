import VersoManual
open Verso.Genre Manual
#doc (Manual) "第8章 形式化の設計と現在の状態" =>

# 状態

本書の幾何学的な主定理とその証明は *Lean で未形式化* である。
Verso のビルドは文書の構文と Lean コード例を確認するが、数学の自然言語部分を証明するものではない。

# 実装の依存グラフ

1. 射影空間の Proj、線束、Euler 列。
2. Čech cohomology と線束の消滅。
3. 基点を持たない $`n+1` 個の一次形式の Koszul 完全列、任意の負捻り線束を作る帰納法。
4. Serre vanishing と大域生成性、hypercohomology spectral sequence による負捻り線束の検出、right orthogonal の消滅、exceptional collection の admissibility と SOD。
5. full strong exceptional collection の定式化。
6. Beilinson 箙の関係式付き経路代数。
7. 抽象的 tilting/dg Morita theorem と finite global dimension。
8. 導来同値の主定理。

# 検証済みの代数的モデル

`Beilinson/Kronecker.lean` は $`n=1` の代数的モデルを
$$`\left\{\begin{pmatrix}a&0&0\\x&b&0\\y&0&b\end{pmatrix}:a,b,x,y\in k\right\}\subseteq M_3(k)`
として構成する。mathlib の行列・部分代数・線形同型・基底を再利用し、
$`k^4` との線形同型、次元4、二頂点の直交冪等元、二本の矢の全ての積を証明した。
積は後から通る道を左から掛ける規約であり、$`e_1\alpha=\alpha=\alpha e_0`、
$`e_0\alpha=\alpha e_1=0`、任意の二本の矢の積は零である。

これは幾何学的な $`\operatorname{End}(\mathcal O\oplus\mathcal O(1))` との同定や、
一般の経路代数構成との同型、加群圏・導来圏の同値をまだ含まない。
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

対象と射の具体的な対応は証明済みだが、圏同値の Lean 構造体はまだ構成していない。
次の目標はこの対応を関手・自然同型として組み立て、有限次元部分圏への制限を示すことである。
証明済み Lean 宣言、外部の既知数学定理、自然言語の証明、未実装の仕様を常に区別する。
