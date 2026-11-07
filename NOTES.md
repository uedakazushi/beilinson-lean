# 研究ノート — 2026-11-07 v0.4

## 数学
- P(V) は lines convention、H^0(O(1)) = V^∨。
- n=0 では全ての O(d) が自明で H^0(O(d))≅k。負捻りの H^0 消滅は n≥1 に限る（第2章に明記）。
- Fullness は対角線の分解を用いず、基点なしの n+1 個の一次形式による Koszul 完全列から O(-k) (k≥0) を帰納的に生成する。O(n-m) で捻ると先頭以外の次数は -m,…,n-m。
- Hom(T,-) は右 End(T) 加群。左箙表現と opposite を区別。Kronecker の α∈e₁Ae₀ は M₁=Me₁ から M₀=Me₀ へ作用する。
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
- 本番の lake-manifest.json は生成・commit 済み。`bash scripts/check.sh` は Lean library / Verso / HTML / LuaLaTeX PDF 生成まで成功。このクラウド環境では TeX Live 2025 の公式配布をユーザー領域に補い、`TEXMFHOME=/workspace/.local/texmf`、`TEXMFVAR=/workspace/.cache/texmf-var`、`TEXMFCONFIG=/workspace/.cache/texmf-config`、`XDG_CACHE_HOME=/workspace/.cache` を指定する。Stacks 実験の依存解決・ビルドは未検証。
- `Beilinson/Kronecker.lean` の行列部分代数モデルは、4要素の基底、次元4、直交冪等元、二本の矢の積を Lean 検証済み。幾何学的な End との同定や一般経路代数との同型は未実装。
- `Beilinson/KroneckerModule.lean` は反対代数から線形自己準同型代数への代数準同型を右作用とし、通常の mathlib Module とも接続する。頂点分解・逆向きの二本の矢・作用の復元・射の可換条件・次元公式を Lean 検証した。`Beilinson/KroneckerCategory.lean` で両方向の関手と自然同型を構成し、`moduleEquivalence` と有限次元対象の `finiteModuleEquivalence` を得た。基礎体の作用は `Module.compHom` による標準の制限を使う。
- `Beilinson/KroneckerResolution.lean` は表現の全射を頂点ごとの全射と同定する。sink(U) と cover(X) の射影性を線形持ち上げで証明し、任意の右加群に短完全な長さ1の射影分解を構成した。有限次元の加群の分解は有限次元に留まる。`rightModule_projectiveDimension_le_one` は全右加群の射影次元が高々1であることを示す。
- 次は頂点射影表現と e₀A、e₁A の明示的同型、および非射影単純加群による上界の鋭さを検証する。
- Beilinson 主定理の Lean proof は未着手。詳細は REUSE.md。
