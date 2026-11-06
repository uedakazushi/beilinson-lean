# 既存形式化の再利用方針 — 2026-11-07 v0.4

## 原則

**実装する前に既存の Lean 定義・補題・定理を調べる。** 順序は (1) 現在 pinned された mathlib、(2) Axiom StacksCore、(3) Axiom StacksFrontier、(4) 他の専門的形式化プロジェクト、(5) 不足する橋渡し補題を新規実装、である。この順序は品質監査の優先順であり、数学的に最適な構成が別なら変更してよい。

他プロジェクトの定理を使えるかどうかは、**単に似た名前があるか**では判断しない。Lean の正確な statement、仮定、型の互換性、定義の意味、依存する axiom、実際の import/build を確認する。探す場所と候補を調査した段階は「実装済み」ではない。

## Axiom Stacks の実情

2026-11-06 の上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` は Lean 4.35.0、mathlib v4.35.0 で、本プロジェクトとバージョンが合う。プロジェクトには約 63,000 モジュールがあり、上流 README も大規模なコンパイル時間・メモリ消費を注意している。

- **StacksCore**: 人間によるレビュー済み。優先して利用。
- **StacksFrontier**: AI 生成・Lean kernel による形式的証明は存在するが、人間による忠実性のレビューは未完了。重要な橋渡し定理では原文の Stacks tag・定式化・仮定を数学的に再確認する。
- `@[stacks TAG]` / `#stacks_tags` と https://stacks.axiommath.ai/ は tag → Lean declaration → import の探索に使う。タグが Mathlib に登録されている場合は Mathlib の定理を優先。

通常の book/Lean ビルドに Stacks 全体を import しない。実験用環境 `integrations/stacks/` は **別 Lake project** で上流を正確な commit に固定しており、通常ビルドの軽さを保つ。これは将来の proof の本番使用を妨げるものではないが、本番での Stacks 依存には再検討・adapter が必要である。実験 probe はまだ実機未検証。

## Beilinson までの再利用対象

| 数学的課題 | 第一候補 | 再利用状況 |
|---|---|---|
| Abel 圏、複体、derived category、t-structure | mathlib（Riou の形式化を含む） | 既存成果の存在は確認、API 未照合 |
| `Proj`、射影空間、tautological bundles | mathlib、Stacks | 候補、定理単位の照合未実施 |
| coherent / quasi-coherent sheaves と比較 | StacksCore → StacksFrontier | 候補、API 未照合 |
| affine/Čech/sheaf cohomology | mathlib、Stacks | 候補、API 未照合 |
| 基点のない線形形式の Koszul 完全列（生成性） | mathlib、Stacks | 候補、API 未照合 |
| Serre vanishing、ample twisting、大域生成性 | mathlib、Stacks | 候補、API 未照合 |
| exceptional collection の admissibility、SOD、right orthogonal | mathlib、Stacks、専門ライブラリ | 候補、API 未照合 |
| perfect complexes、derived tensor、pushforward | mathlib、Stacks | 候補、API 未照合 |
| quiver、path algebra、representations | mathlib の行列・部分代数・基底 | n=1 の行列モデルと右作用・逆向きの矢・射の具体的な対応を Lean 検証。一般経路代数との同型や圏同値の構造体は未実装 |
| exceptional collections / tilting | Axiom BondalThomsen 等 | 関連プロジェクトを確認、再利用可能性は未確認 |
| dg enhancement / derived Morita | mathlib、Stacks、外部専門ライブラリ | 実装範囲は未確認 |
| Beilinson equivalence | 未確認 | 本研究の目標であり、実装済みと扱わない |

## 外部プロジェクト

- Axiom Stacks: https://github.com/AxiomMath/Stacks （検証対象 commit は上記）
- Stacks tag explorer: https://stacks.axiommath.ai/
- mathlib: https://github.com/leanprover-community/mathlib4 （本番 v4.35.0）
- Joël Riou, derived categories in mathlib: https://github.com/joelriou/lean-derived-categories （論文への cross-reference project。標準導来圏コードは mathlib を先に検索）
- Axiom BondalThomsen: https://github.com/AxiomMath/BondalThomsen （exceptional 系の関連候補。Beilinson への API 互換性は未確認）

## 定理の再利用の記録形式

必要な定理が特定できた場合のみ、ここに簡潔に追記・統合する：

- 数学的主張（仮定付き）
- Stacks tag / Mathlib declaration / source URL（正確なもの）
- import module と上流 revision
- Lean の statement の数学的監査結果（Core/Frontier の区別）
- `#check`・`lake build` の実施状況
- 本研究のどの補題が依存するか

大規模な検索ログや Stacks のコピーは保存しない。未確認の tag や Lean declaration は推測で追加しない。

## n=1 の代数モデルで再利用した API

本番 mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`（v4.35.0）：

- `Subalgebra`：`Mathlib.Algebra.Algebra.Subalgebra.Basic`。行列の集合がスカラー・加法・乗法で閉じることを証明し、環と代数の構造を継承する。
- `LinearEquiv.finiteDimensional`：`Mathlib.LinearAlgebra.FiniteDimensional.Defs`、`LinearEquiv.finrank_eq`：`Mathlib.LinearAlgebra.Dimension.Finrank`。体と線形同型の仮定から有限次元性と次元の一致を移す。
- `Module.Basis.map`、`Pi.basisFun`：`Mathlib.LinearAlgebra.StdBasis`。座標空間の標準基底を線形同型で移す。

`Beilinson/Kronecker.lean` はこれらを利用し、任意の体 k に対して `Beilinson.Kronecker.coordinates`、`finrank`、`basis`、`coordinates_mul` および頂点・矢の積を証明した。合成は後の写像を左に置き、矢は e₁Ae₀ に属する。幾何学的 End との同型と一般経路代数との同型は未実装。Stacks には依存しない。Kronecker の両ファイルの全ての名前付き定義・定理について `#print axioms` を確認し、依存は標準の `propext`、`Classical.choice`、`Quot.sound` の範囲で、`sorryAx` や独自公理はない。

## 右作用と逆向きの矢の bridge

同じ pinned mathlib で次の API を再利用する：

- `Algebra.lsmul`：`Mathlib.Algebra.Algebra.Tower`。k-加群 M と Aᵐᵒᵖ-加群 M に、`IsScalarTower k Aᵐᵒᵖ M` と `SMulCommClass Aᵐᵒᵖ k M` を仮定し、作用を `Aᵐᵒᵖ →ₐ[k] Module.End k M` として取り出す。
- `Module.compHom`：`Mathlib.Algebra.Module.RingHom`。線形自己準同型への環準同型から加群構造を得る。構成した右作用について ground-field の scalar tower と作用の可換性を別途証明し、`actionOfModule_ofArrows` で往復を確認する。
- `LinearMap.prodMap`：`Mathlib.LinearAlgebra.Prod`。頂点ごとの射を直積上の線形写像にする。
- `Module.finrank_prod`：`Mathlib.LinearAlgebra.Dimension.Constructions`。有限次元の頂点空間の次元を加える。

`Beilinson/KroneckerModule.lean` の `ofArrows` は任意の二本の線形写像 V₁→V₀ から右作用を作る。任意の右作用 ρ について `decompose_action` は M≃M₀×M₁ が元の作用と復元した作用を絡み合わせることを証明する。`prodMap_intertwines_iff` は射の条件を二本の可換な正方形と同定し、`vertexMap_arrow` と `decompose_intertwiner` は一般の intertwiner が頂点の写像に分解されることを示す。`finrank_vertices` は M が有限次元のとき dim M=dim M₀+dim M₁ を与える。

これらは対象・射の具体的な対応であり、`CategoryTheory.Equivalence` の構造体を構成したという意味ではない。幾何学的な層の圏や導来圏との同値にもまだ依存しない。

## 更新と再現

本番は root `lean-toolchain`, `lakefile.toml` と実生成 `lake-manifest.json` に固定する。Stacks は独立環境で revision を固定し、統合検証に成功した場合にのみ必要な範囲を本番へ移す。上流 63k モジュールの更新に通常の Verso ビルドを従属させない。
