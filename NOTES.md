# 研究ノート — 2026-11-07 v0.4

## 数学
- P(V) は lines convention、H^0(O(1)) = V^∨。
- Fullness は対角線の分解を用いず、基点なしの n+1 個の一次形式による Koszul 完全列から O(-k) (k≥0) を帰納的に生成する。O(n-m) で捻ると先頭以外の次数は -m,…,n-m。
- Hom(T,-) は右 End(T) 加群。左箙表現と opposite を区別。
- strong exceptional と full の証明を分離する。
- derived Morita はまず Perf(A) の同値であり、有限次元加群の有界導来圏との比較には finite global dimension が必要。
- Serre vanishing と大域生成性により O(-k) への全 Hom が消える対象は零。SOD の right orthogonal が零から fullness を導くには、例外集合の生成する部分圏の admissibility を使う。Čech cohomology と dg Morita の正確な仮定も精査する。

## 既存形式化を使う際の障害
- Stacks は human-reviewed Core と kernel-checked AI Frontier を区別する。Frontier 利用では theorem statement の意味と原 Stacks tag を監査する。
- 63k 程度のモジュールを通常ビルドに追加すると開発速度が下がる可能性がある。選択的 import と分離した実験 Lake project でまず評価する。
- 数学的に既存の結果があることと、実際に mathlib/Stacks の定理の型を合成できることは別問題。正確な declaration/import/依存を照合する。
- mathlib の derived category API と Stacks の各種 derived/cohomology API の間の bridge が必要かは未確認。

## 技術的状態
- root の Lean/mathlib/Verso v4.35.0、および upstream Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 の toolchain/mathlib v4.35.0 を確認。
- 本番・Stacks 実験とも lake-manifest.json の生成と実ビルドは未実施。
- Beilinson 主定理の Lean proof は未着手。詳細は REUSE.md。
