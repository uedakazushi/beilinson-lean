# 研究方針 — 2026-11-08 v0.5

## 現時点の目標
自然言語の Beilinson 定理の Verso 教科書を完成させ、既存形式化を最大限再利用して Lean 4 で三角圏同値を形式化する。達成基準は自足的な数学的証明と、主定理・必要な依存補題について sorry-free かつ数学的意味を監査した Lean proof。

## 現在の到達点

生成性の自然言語の証明は、対角線の resolution を使わず、負捻りの Koszul 帰納法と SOD の right orthogonal の消滅に置き換えた。Book/ は Verso の日本語教科書、Beilinson/ は Stacks に依存しない本番ライブラリである。Lean/mathlib/Verso v4.35.0 と、独立 Stacks project の上流 revision を固定し、本番の library / HTML / LuaLaTeX PDF 生成を検証している。

本番では具体的 Kronecker 代数、右加群と逆向き表現の圏同値、有限次元部分圏、長さ1の射影分解と射影次元、一般の線形圏での End 同定、Hom 前合成の作用、有限次元加群の Serre 性と被覆条件、有界 devissage を検証した。

独立環境では40ターゲットを検証した。全次元で実際の D^b(有限次元右 Beilinson 行列代数加群) から D^b(Coh Pⁿ) 自体への三角同値を両方向で確認した。非有界 dg Beilinson 同値を通常右 End(E) 加群へ移し、全ての次元で compact 始域から実際の D^b(Coh Pⁿ) への三角同値を構成した。n=1 では実際の負の窓の End(E) と Kronecker 代数を同定し、D^b(有限次元右 Kronecker 加群) 自体から D^b(Coh P¹) 自体への三角同値を両方向で確認した。通常加群への移送の現状の universe は Type 0 である。任意の可換環・全次元で E(n)≅T と、捻りによる End の代数同型も確認した。

## 現在の核心と優先順位

1. `PositiveEndBounded.equivalence` と、別定義の古典的 RHom・導来 tensor 関手を明示的な自然同型で比較する。始域・終域は既に本文と一致し、別モジュールからも検証した。
2. 検証済みの実際の有界導来捻りと、右 End 加群値 Hom の複体上の自然同型を、全加群の導来モデルと dg Hom の計算へ接続する。
3. 検証済みのモデルと三角の規約を保ち、コホモロジーの基礎体上の線形構造を明示して、既存の有限 total Hom 判定や代数の compactness 判定を再利用する。
4. 本文の Čech、Koszul、admissibility / SOD、導来 Hom–tensor 随伴の説明と、完成した Lean 宣言の範囲を同期する。
5. 本番と独立 Stacks 環境のチェックを継続し、正確な宣言・仮定・依存公理・ビルドコストを REUSE.md に記録する。

## 現行の技術方針
Book/ と Beilinson/ を分離した一つの本番 Lake project。Lean/mathlib/Verso の更新は意図的に固定・検証してから行う。Stacks は巨大なので実験用の別 Lake project で調査し、必要な定理と現実的なビルド負担が確認された時点で本番依存を再評価する。既存の定義や定理を無用にコピーしない。REUSE.md を軽量な再利用台帳とし、API/数学的仮定・人間レビュー・ビルド状況を区別する。GitHub Actions は使わない。検証後の成果は main に直接 push し、作業用ブランチや PR は作成しない。

## 研究運営の一般原則
数学的重要性・新規性・理解の深化・応用可能性・正確性・実現可能性を総合して方針を柔軟に更新する。証明済み、追加仮定付き、未完成、予想、計算観察を厳密に分け、原稿上の証明と Lean kernel の確認、数学的な statement の監査を区別する。先行研究は一次資料を確認して引用し、確認できない情報を推測しない。現行の教科書と研究ノートへ有効な成果を統合し、更新履歴・旧版・重複ファイルは残さない。研究継続 bundle は現行の方針、研究ノート、教科書と再現に不可欠な最小のソース・依存関係だけで構成し、数学的内容を減らさない。研究の区切りごとに追加承諾を求めず Library 保存してよいが、Library 上の既存ファイルの削除は明示指示がない限り行わない。ファイル生成、検証、GitHub 登録、Library 保存を別々の状態として扱う。

## 再開方法
このファイル → REUSE.md → Book.lean / Book/ → NOTES.md → Beilinson/ → integrations/stacks/README.md の順に読む。

全次元の有限次元始域は `MatrixBeilinson.equivalence` で接続した。`MatrixAlgebraComparison` の同じ部分代数としての比較、幾何学的 End の同定、有限次元代数に対する一般的な Serre 有界導来比較を使う。残る中心課題は正の窓の導来 tensor/Hom 関手全体との照合である。

正の窓も `PositiveEndBounded.equivalence` で、実際の有限次元右 End(T) 加群からの三角同値に接続した。行列–End 同型は基礎体上の代数同型として確認し、有限次元加群の有界導来圏自体を移す。残る関手の照合は独立した課題として明記する。
