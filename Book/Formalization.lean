import VersoManual
open Verso.Genre Manual
#doc (Manual) "第8章 形式化の設計と現在の状態" =>

# 状態

本書の自然言語の証明は **Lean で未形式化** である。
Verso のビルドは文書の構文と Lean コード例を確認するが、数学の自然言語部分を証明するものではない。

# 実装の依存グラフ

1. 射影空間の Proj、線束、Euler 列。
2. Čech cohomology と線束の消滅。
3. 対角線の正則切断、Koszul exactness、投影公式。
4. full strong exceptional collection の定式化。
5. Beilinson 箙の関係式付き経路代数。
6. 抽象的 tilting/dg Morita theorem と finite global dimension。
7. 導来同値の主定理。

最初の小さな実装目標は $`n=1` の Kronecker 箙の有限次元代数としての構成である。
証明済み Lean 宣言、外部の既知数学定理、自然言語の証明、未実装の仕様を常に区別する。
