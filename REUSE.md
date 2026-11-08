# 既存形式化の再利用方針 — 2026-11-08 v0.5

## 原則

**実装する前に既存の Lean 定義・補題・定理を調べる。** 順序は (1) 現在 pinned された mathlib、(2) Axiom StacksCore、(3) Axiom StacksFrontier、(4) 他の専門的形式化プロジェクト、(5) 不足する橋渡し補題を新規実装、である。この順序は品質監査の優先順であり、数学的に最適な構成が別なら変更してよい。

他プロジェクトの定理を使えるかどうかは、**単に似た名前があるか**では判断しない。Lean の正確な statement、仮定、型の互換性、定義の意味、依存する axiom、実際の import/build を確認する。探す場所と候補を調査した段階は「実装済み」ではない。

## Axiom Stacks の実情

2026-11-06 の上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` は Lean 4.35.0、mathlib v4.35.0 で、本プロジェクトとバージョンが合う。プロジェクトには約 63,000 モジュールがあり、上流 README も大規模なコンパイル時間・メモリ消費を注意している。

- **StacksCore**: 人間によるレビュー済み。優先して利用。
- **StacksFrontier**: AI 生成・Lean kernel による形式的証明は存在するが、人間による忠実性のレビューは未完了。重要な橋渡し定理では原文の Stacks tag・定式化・仮定を数学的に再確認する。
- `@[stacks TAG]` / `#stacks_tags` と https://stacks.axiommath.ai/ は tag → Lean declaration → import の探索に使う。タグが Mathlib に登録されている場合は Mathlib の定理を優先。

通常の book/Lean ビルドに Stacks 全体を import しない。実験用環境 `integrations/stacks/` は **別 Lake project** で上流を正確な commit に固定しており、通常ビルドの軽さを保つ。これは将来の proof の本番使用を妨げるものではないが、本番での Stacks 依存には再検討・adapter が必要である。35ターゲットの実 import/build に成功した。非有界 dg 同値、通常右加群への移送、compact 始域の有界版と、n=1 の実際の有界導来圏間の三角同値を検証済み。

## Beilinson までの再利用対象

| 数学的課題 | 第一候補 | 再利用状況 |
|---|---|---|
| Abel 圏、複体、derived category、t-structure | mathlib（Riou の形式化を含む） | 既存成果の存在は確認、API 未照合 |
| `Proj`、射影空間、tautological bundles | mathlib、Stacks | 候補、定理単位の照合未実施 |
| coherent / quasi-coherent sheaves と比較 | StacksCore → StacksFrontier | 候補、API 未照合 |
| affine/Čech/sheaf cohomology | mathlib、Stacks | 候補、API 未照合 |
| 基点のない線形形式の Koszul 完全列（生成性） | StacksFrontier | 座標 Koszul の完全性を専用 probe で検証済み。導来圏内の生成性への移送は未実装 |
| Serre vanishing、ample twisting、大域生成性 | mathlib、Stacks | 候補、API 未照合 |
| exceptional collection の admissibility、SOD、right orthogonal | StacksFrontier、mathlib | finite total Hom と右直交零検出からの充満性を専用 adapter で検証済み。幾何学的仮定は未証明 |
| perfect complexes、derived tensor、pushforward | mathlib、Stacks | 候補、API 未照合 |
| quiver、path algebra、representations | mathlib の行列・部分代数・基底 | n=1 の行列モデルと右作用・逆向きの矢・射の具体的な対応を Lean 検証。具体的モデルについて全加群と有限次元加群の圏同値を構成済み。一般経路代数との同型は未実装 |
| exceptional collections / tilting | StacksFrontier、Axiom BondalThomsen | Koszul 生成性・非有界 dg 同値を実ビルド。通常加群への比較と compact 始域の有界版も検証済み |
| dg enhancement / derived Morita | StacksFrontier | `Beilinson.beilinson_equivalence` は非有界 dg 加群と準連接導来圏の同値。実ビルド・公理監査済み。Type 0 で compact な通常右 End 加群から D^b(Coh) への比較を検証済み |
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

`Beilinson/Kronecker.lean` はこれらを利用し、任意の体 k に対して `Beilinson.Kronecker.coordinates`、`finrank`、`basis`、`coordinates_mul` および頂点・矢の積を証明した。合成は後の写像を左に置き、矢は e₁Ae₀ に属する。幾何学的 End との同型と一般経路代数との同型は未実装。Stacks には依存しない。Kronecker の代数・作用のファイルの名前付き定義・定理と、圏同値・射影分解・射影次元の主要宣言について `#print axioms` を確認し、依存は標準の `propext`、`Classical.choice`、`Quot.sound` の範囲で、`sorryAx` や独自公理はない。

## 右作用と逆向きの矢の bridge

同じ pinned mathlib で次の API を再利用する：

- `Algebra.lsmul`：`Mathlib.Algebra.Algebra.Tower`。k-加群 M と Aᵐᵒᵖ-加群 M に、`IsScalarTower k Aᵐᵒᵖ M` と `SMulCommClass Aᵐᵒᵖ k M` を仮定し、作用を `Aᵐᵒᵖ →ₐ[k] Module.End k M` として取り出す。
- `Module.compHom`：`Mathlib.Algebra.Module.RingHom`。線形自己準同型への環準同型から加群構造を得る。構成した右作用について ground-field の scalar tower と作用の可換性を別途証明し、`actionOfModule_ofArrows` で往復を確認する。
- `LinearMap.prodMap`：`Mathlib.LinearAlgebra.Prod`。頂点ごとの射を直積上の線形写像にする。
- `Module.finrank_prod`：`Mathlib.LinearAlgebra.Dimension.Constructions`。有限次元の頂点空間の次元を加える。

`Beilinson/KroneckerModule.lean` の `ofArrows` は任意の二本の線形写像 V₁→V₀ から右作用を作る。任意の右作用 ρ について `decompose_action` は M≃M₀×M₁ が元の作用と復元した作用を絡み合わせることを証明する。`prodMap_intertwines_iff` は射の条件を二本の可換な正方形と同定し、`vertexMap_arrow` と `decompose_intertwiner` は一般の intertwiner が頂点の写像に分解されることを示す。`finrank_vertices` は M が有限次元のとき dim M=dim M₀+dim M₁ を与える。

これらの対象・射の対応を、次節のファイルで圏同値へ組み立てる。幾何学的な層の圏や導来圏との同値にはまだ依存しない。

## 圏同値と有限次元部分圏

同じ pinned mathlib の次の API を使用する：

- `ModuleCat`、`ModuleCat.ofHom`、`LinearEquiv.toModuleIso`：`Mathlib.Algebra.Category.ModuleCat.Basic`。反対代数の通常の加群を始域とし、線形写像・同型を圏の射・同型へ移す。
- `NatIso.ofComponents`：`Mathlib.CategoryTheory.NatIso`（`Equivalence` から import）。成分ごとの同型と自然性を自然同型へ組み立てる。
- `CategoryTheory.Equivalence.mk`：`Mathlib.CategoryTheory.Equivalence`。両方向の関手と自然同型から三角恒等式を満たす圏同値を構成する。単位は mathlib の adjointification により調整され得る。
- `CategoryTheory.Equivalence.congrFullSubcategory`：`Mathlib.CategoryTheory.ObjectProperty.Equivalence`。終域の対象の性質が同型で不変であり、その逆像が始域の性質と一致するとき、充満部分圏の圏同値を得る。

`Beilinson/KroneckerCategory.lean` の `ReverseRep` は二つの k-ベクトル空間と二本の V₁→V₀ の線形写像の圏であり、射は可換な頂点ごとの線形写像。`moduleEquivalence` は mathlib の `ModuleCat (Algebra k)ᵐᵒᵖ` とこの圏を同値にする。基礎体の作用には代数準同型からの `Module.compHom` と `IsScalarTower.of_compHom` を用いる。

`finite_toReverseRep_iff` は基礎体上の有限次元性と両頂点の有限次元性を同定する。`finiteModuleEquivalence` はこの性質の充満部分圏の間の圏同値。有限次元性が表現の同型で不変であることは、同型の頂点写像の全射性と `FiniteDimensional.of_surjective` で確認した。全体と有限次元部分圏の両圏同値はビルド済み・依存公理監査済み。具体的モデルと幾何学的 End の同定、一般経路代数との同型、導来同値は含まない。

## 長さ1の射影分解と射影次元

同じ pinned mathlib の次の宣言を使用する：

- `CategoryTheory.Projective`：`Mathlib.CategoryTheory.Preadditive.Projective.Basic`。任意の全射に対して射を持ち上げるという仮定で射影対象を定義する。
- `Module.projective_lifting_property`：`Mathlib.Algebra.Module.Projective`。射影加群からの線形写像を全射に沿って持ち上げる。体上のベクトル空間の既存の自由性・射影性インスタンスを使用する。
- `CategoryTheory.Equivalence.map_projective_iff`：`Mathlib.CategoryTheory.Preadditive.Projective.Basic`。圏同値が射影対象を保存・反映することを利用して、表現側の射影性を加群圏へ移す。
- `ModuleCat.shortComplex_shortExact`：`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`。写像の単射性、全射性、`Function.Exact` から加群圏の短完全列を得る。
- `ShortComplex.isoMk`、`ShortComplex.shortExact_of_iso`：`Mathlib.Algebra.Homology.ShortComplex.Basic` および `ShortExact`。終点を頂点分解から元の加群に戻す同型で短完全性を移す。
- `projectiveDimension_le_iff`、`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃`：`Mathlib.CategoryTheory.Abelian.Projective.Dimension`。短完全列の射影次元の不等式から、任意の右加群 M の `projectiveDimension M ≤ 1` を得る。

`Beilinson/KroneckerResolution.lean` は sink(U)=(U,0) と、cover(X)=(X₀×(X₁×X₁),X₁) を用いる。augmentation の頂点0での写像は (u,s,t)↦u+f₀s+f₁t、関係写像は (s,t)↦(-f₀s-f₁t,s,t)。前者の全射性、後者の単射性と像=核を直接確認する。射影性は極小な射影被覆の存在ではなく持ち上げ性で証明する。

`rightModuleResolution`、`rightModuleResolution_shortExact`、両項の射影性、`finite_rightModuleResolution_terms`、`rightModule_projectiveDimension_le_one` を Lean 検証した。これは任意の体・任意の右加群についての上界であり、上界の鋭さは次節で検証済み。Ring の global-dimension API との同定は未実装。eᵢA との同型は下記で検証済み。一般 n の幾何学的・導来圏の主張も含まない。

## 上界を達成する単純加群

`Beilinson/KroneckerDimension.lean` は L=(0,k;0,0) の標準射影全射に切断がないことを、第一の矢への可換性から示す。`Projective.factors` を否定することで非射影性を得て、圏同値で通常の右加群へ移す。

単純性は `isSimpleModule_iff_toSpanSingleton_surjective`（`Mathlib.RingTheory.SimpleModule.Basic`）を用いる。右加群の全ての非零ベクトルが全体を生成することを、頂点1の係数 w/v による作用で確認する。射影次元の下界は `projectiveDimension_ge_iff` と `projective_iff_hasProjectiveDimensionLT_one`（`Mathlib.CategoryTheory.Abelian.Projective.Dimension`）で非射影性から導き、既存の上界と合わせる。`sourceSimpleModule_projectiveDimension` は正確に射影次元1を主張する。`sourceSimpleModule_finite` により例が有限次元であることも確認した。

## 頂点右イデアル

`Beilinson/KroneckerIdeals.lean` は、正則右加群の部分加群 `{a | e*a=a}` と冪等元が生成する右イデアル eA の一致を `mem_fixedLeft_iff` で示す。`sinkIdealEquiv` と `sourceIdealEquiv` は Aᵐᵒᵖ-線形同型として、e₀A と sink(k)、e₁A と source(k) をそれぞれ同定する。`vertexIdealDecomposition` は A≃e₀A×e₁A を右加群同型として与える。

射影性の移送には `CategoryTheory.Projective.of_iso`（`Mathlib.CategoryTheory.Preadditive.Projective.Basic`）を再利用する。source 表現は単純表現の標準射影全射の始域から自明な零成分を除いた表現と同型である。通常の加群としての `Module.Projective` は `ModuleCat.projective_of_module_projective`（`Mathlib.Algebra.Category.ModuleCat.Projective`）で得る。この変換の Small 仮定はここでは環・加群を同じ universe u に置いて満たす。明示的同型・射影性・正則加群分解はビルドと公理監査の対象である。

## Stacks の充満性・幾何学 probe

すべて上記の固定 revision の `StacksFrontier`。以下の数学的照合とローカル kernel check は、上流の人間レビュー済みへの昇格を意味しない。

- `CategoryTheory.Pretriangulated.prop_of_hasFiniteTotalHom_of_exceptional`、import `StacksFrontier.CategoryTheory.Triangulated.ExceptionalCollectionFiniteness`。有限列 G の各自己準同型が scalar、非零自己シフト Hom が零、逆順の全シフト Hom が零、必要な total Hom が有限、右直交が零を検出するという仮定から、G を含む strictly full triangulated subcategory が対象 M を含むと結論する。`HasFiniteTotalHom` は各次数の有限次元性に加え非零次数が有限であることも要求する。Tag [0FYB](https://stacks.math.columbia.edu/tag/0FYB) に関連する抽象的部分であり、幾何学的 tag 全体の形式化ではない。`StacksProbe.full_of_exceptional_and_detection` は ambient subcategory を全体に取った adapter。実 package import/build と公理監査に成功。
- `Stacks.AlgebraicGeometry.ProjKoszulComplex.acyclic_koszulComplex`、import `StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.Exactness`。任意の可換環 A、n≥0、a∈ℤ に対し、多項式環の全次数 Proj 上で O(a+j) の座標 Koszul cochain complex が acyclic。標準開集合上で一つの座標比が1となることを使う stalk contracting homotopy による証明で、完全性自体を仮定していない。`StacksGeometryProbe.coordinate_koszul_acyclic` の実 import/build と公理監査に成功。Stacks 側の import 閉包は92モジュール。
- `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic`、import `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange`。基底 scheme S、n=m+1≥1、-n≤d<0、q∈ℤ について R^q f_* O(d)=0。Tag [01XW](https://stacks.math.columbia.edu/tag/01XW) の各行の既存結果を合成する定理で、この宣言自身への tag 属性はない。`StacksCohomologyProbe` の実 build・標準3公理の監査に成功した（閉包2125モジュール）。

重要な型の境界：Koszul は多項式 Proj、higher direct image は整数上の射影空間を基底変換したモデルを使う。両者の同一視はまだ adapter に含めていない。`TwistGenerator.Negative` は自明化開集合上の線束の生成切断であり、導来圏の右直交零検出を直接述べる定理ではない。多項式 Proj 側の Koszul 生成性と零検出、および非有界 dg 同値は別の経路で検証済みである。基底変換モデルとの比較を暗黙に消してはいない。

上記の検証済み adapter の依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。root の production dependency は変更しない。専用 manifest を `integrations/stacks/` に保存する。

## 検証した生成性・dg 同値

以下は正確なソースと証明経路を確認した結果。宣言ごとにローカル build 状態を区別する。

- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul` の `Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen`。多項式 Proj 上で E=O⊕O(-1)⊕…⊕O(-n) とし、全ての m≥0 で O(-m) が `gen E` に属する。証明は座標 Koszul の stupid filtration による有限 cone と強い帰納法で、対角線の分解を使わない。閉包228モジュール。`StacksGenerationProbe.negative_twist_generated` と `negative_twist_orthogonal` の実 import/build・公理監査に成功。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.KoszulQuasiCoherent` の `isWeakTriangulatedGenerator_twistSumDerivedQCoh`（同 namespace、Tag [0A9V](https://stacks.math.columbia.edu/tag/0A9V)）。Koszul 生成性と ample 負捻りの零検出を多項式 Proj 上で接続する。この経路なら基底変換モデルのコホモロジーとの比較を経ず生成性を進められる。閉包2378モジュール。非有界同値の依存として実ビルド済み。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear` の `Stacks.AlgebraicGeometry.Beilinson.beilinson_equivalence`（Tag [0BQU](https://stacks.math.columbia.edu/tag/0BQU)）。任意の可換環 A と n≥0 に対し、上記 E の dg 自己準同型代数 R からの derived tensor が D(R) と D_QCoh の A-線形三角同値を与え、正則加群を E に送る。定理の仮定に同値性自体は含まれない。ソースは生成性、compactness、正則加群間の Hom の同型から導く。閉包8353モジュール。`StacksBeilinsonProbe` の実 build と標準3公理の監査に成功した。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEndAlgebra` の `Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquiv`、`endAlgebra_d_eq_zero`、`endAlgebra_grading_eq_bot` は R が通常の End(E) に集中することを述べる。既存の `DifferentialGradedModule.degreeZeroDerivedEquivalence`（import `StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra`）は degree-zero DGA の右加群を通常の反対環の加群の複体へ比較する。`StacksOrdinaryProbe.rightModuleComparison` と `rightModuleComparison_exact` で、任意の非可換 R-代数 S の degree-zero DGA から Sᵐᵒᵖ の加群の導来圏への同値と三角の保存を検証済み。上流と同じ局所 pretriangulated instance を明示する必要があった。依存公理は標準の3つのみ。幾何学側との接続は `ConcentratedDGA` と `OrdinaryBeilinson` で Type 0 の場合に検証済み。

- import `StacksFrontier.Homology.Perfect.BeilinsonAlgebra` の `StacksDraft.Perfect.hasFiniteTotalCohomology_iff_isCompactObject` は、多項式の斉次成分から作る上三角行列 Beilinson 代数の右加群の導来圏で、compactness と有限 total cohomology の同値を述べる。閉包96モジュール。`StacksAlgebraProbe.compact_iff_finite_total_cohomology` の実 import/build と公理監査に成功。依存公理は標準の3つのみ。幾何学的 End との同型はこの定理に含まれない。

教科書の T=O⊕O(1)⊕…⊕O(n) は上記 E を O(n) で捻り、直和を逆順に並べたもの。従って数学的には対応するが、通常右 End(E) 加群への比較と compact 始域の bounded coherent 制限は検証済みである。E(n)≅T と End の移送は `PositiveWindow` で検証した。全次元の有限次元右行列代数加群の有界導来圏からの移送は `MatrixBeilinson` で接続した。正の窓の導来関手全体の比較は残る。非有界 dg 版の既存定理を、そのまま本書の完成した主定理とは呼ばない。

## dg 代数を degree-zero モデルに接続する adapter

`integrations/stacks/DGAComparison.lean` の `Beilinson.DGAComparison.degreeZeroIso` は、可換基礎環 R、R 上の dg 代数 B、通常の R-代数 S と代数同型 B.A≃ₐ[R]S を取り、全ての元が次数0、非零次数の成分が零、微分が零であるという明示的仮定から B≅degreeZero R S を構成する。相互に逆な二つの dg 射を構成し、通常の環同型だけで dg 同型と見なしていない。

既存の `DifferentialGradedAlgebra` の圏と `degreeZero` を再利用する薄い adapter であり、上流コードの複製ではない。import は `StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory` と `StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra`。閉包456モジュール。実 build と公理監査に成功し、依存公理は標準の3つのみ。幾何学的 End の同型への具体的適用は、大きな幾何学側の検証ターゲットで別途確認する。

## dg 導来圏の三角の符号を合わせる adapter

重要な追加境界：幾何学的 `Beilinson.tensorWithGenerator` は `DifferentialGradedModule.derivedCategory`（cone 規約）を始域に持つ。一方 `degreeZeroDerivedEquivalence_functor_exact` は `derivedCategory'`（admissible short exact sequence 規約）について述べる。同じ universe では基礎圏・quasi-isomorphism の条件は definitionally 一致するが、三角構造をそのまま混用してはいけない。

既存の import `StacksFrontier.Algebra.DifferentialGraded.Module.ConeSignTransfer` は、二つの規約が第三の矢の符号で異なることを `mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_signTwist_mapTriangle` として形式化し、`isTriangulated_signTwist_comp` を提供する。通常の恒等関手と、shift 比較が (-1)^n である sign-twisted identity は同じものとして扱わない。

新しい `integrations/stacks/DegreeZeroConeComparison.lean` はこの既存結果を使う。`signedHomotopyFunctor_isTriangulated` で sign twist 後の homogeneous-components functor が cone 規約で exact となることを示し、局所化を通して `coneRightModuleComparison_exact` を得た。基礎圏の比較を新しい shift 比較とともに降ろすので、単に primed の定理を型変換して exact と呼んでいない。実 build と公理監査に成功し、依存は標準の3つのみ。

## 集中 dg 代数から通常右加群への直接比較

`integrations/stacks/ConcentratedDGA.lean` の `eq_degreeZero_self` は、次数0への集中・非零次数成分の消滅・微分零を仮定し、基礎の R-代数 B.A を保つとき B=degreeZero R B.A を証明する。grading の分解データもその逆写像の一意性から一致させており、構造の等式を仮定していない。

`comparison` はこの等式に沿って cone 規約の比較を輸送し、通常右 B.A-加群の標準導来圏への圏同値、shift 比較、三角の保存をデータとしてまとめる。`Comparison.inverse_isTriangulated` により、整合的な shift 比較を選んだ逆関手も exact。追加の dg Morita / quasi-isomorphism による代数変更定理を必要としない。実 build と公理監査に成功し、主要宣言は標準の3公理のみを使う。Stacks 側の import 閉包は462モジュール。幾何学的 endAlgebra に具体的に代入する検証はなお別ターゲットで行う。

## n=1 の End 同定に向けた二対象の計算

本番 `Beilinson/KroneckerEnd.lean` は Stacks に依存しない。k-線形 preadditive 圏で binary biproducts を仮定する。`ofArrows` は二本の射 X→Y から具体的 Kronecker 代数の単位的な代数準同型 A→End(X⊞Y) を構成する。

`algebraEquiv` の追加仮定は、Hom(X,X)≃ₗ[k]k と Hom(Y,Y)≃ₗ[k]k（各恒等射を1へ送る）、Subsingleton Hom(Y,X)、および Hom(X,Y) の Fin 2 基底。4成分の座標抽出と再構成を示して全単射性を証明し、`ofArrows` の乗法保存で代数同型へ昇格する。`ofArrows_e₀`、`ofArrows_e₁`、`ofArrows_arrow` は生成元の像を射影・包含と選んだ射として確認し、`finiteDimensional` と `finrank` は条件付き End の有限次元性と次元4を与える。この一般補題には仮定が残るが、射影直線への代入は後述の `ProjectiveLineEnd` で検証した。

再利用した pinned mathlib API：`Biprod.ofComponents`、`Biprod.ofComponents_comp`、`Biprod.ofComponents_eq`（`Mathlib.CategoryTheory.Preadditive.Biproducts`）、`CategoryTheory.End` とその `asHom` / `of`、`Module.Basis.sum_repr`、`AlgHom.ofLinearMap`、`AlgEquiv.ofLinearEquiv`。End は Hom の単なる略記ではないため、morphism の計算へは `asHom` で移す。主要宣言の実 build と公理監査に成功し、依存は標準の3公理のみ。

ライブラリ入口は `module` / `public import` を使い、新しい module クライアントからの公開 API を確認する。空の Foundation の Mathlib umbrella import は最小限の category import へ整理し、数学ファイルが個別の依存を持つ。

## 標準の Hom 右作用と射影分解への接続

`Beilinson/KroneckerYoneda.lean` の `homFunctor` は mathlib の `preadditiveCoyonedaObj (X⊞Y)` と、`ofArrows` の反対環準同型に沿う `ModuleCat.restrictScalars` の合成である。独自に作用を置いて標準の End 作用との一致を仮定していない。`homCoordinates_precompose` は二成分への線形分解が `Kronecker.ofArrows` の作用を保つことを示す。`homModuleEquiv` は通常の反対代数加群の線形同型で、`homFunctorIso` は二つの Hom を頂点に持つ `representationFunctor` と `fromReverseRep` の合成への自然同型である。

`Beilinson/KroneckerEndModules.lean` は任意の環同型 A≃S に対して `restrictScalarsEquivalenceOfRingEquiv` を使う。`resolution` の短完全性は `ShortExact.map_of_exact`、両項の射影性は `Equivalence.map_projective_iff` で移送し、`resolutionTargetIso` で終点を元の加群に戻す。`projectiveDimension_le_one` と条件付きの `end_projectiveDimension_le_one` はこの実際の短完全列から得る。これらも本番の build と標準3公理の監査に成功した。

## 幾何学側の compactness と有界 coherent の接続

`GeometricPerfectProbe.compact_iff_boundedCoherent` は、qcqs な正則スキーム X に対して、locally small な D_QCoh の compact 対象と有界 coherent コホモロジーを持つ対象を同定する。前半は `Stacks.Duality.QcqsPerfect.isCompactObject_iff_isPerfect`（09M1、`AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsCompactIsPerfect`）、後半は `Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular`（0FDC、`…Perfect.RegularBoundedCoherentPerfect`）。二つの perfect の定義は Scheme の RingedSpace.{u,u} で定義上同じであることを確認した。derived-category model は `Scheme.Modules.hasDerivedCategory` に揃える。

`ProjectivePerfectProbe.regular` は `…Variety.Projective.RegularProjectiveSpace` の `ProjPolyChart.isRegularLocalRing_stalk_proj` と `…ProjNoetherian.Basic` の Noetherian 性を `AlgebraicGeometry.isRegular_tfae` で組み合わせる。`compact_iff_boundedCoherent` は任意の体、全ての n≥0 の多項式 Proj への代入である。両ターゲットの実 build と標準3公理の監査に成功した。

これは幾何学側の対象条件の確認である。Beilinson 関手の制限、代数側の有限次元条件、Db(Coh) 自体と D_QCoh 内の有界 coherent 対象の比較は別に必要である。

## 非可換な代数側の有界 devissage

本番 `Beilinson/DerivedDevissage.lean` は mathlib のみを使う。`of_bounded_cohomology` と `of_isBounded` は、任意のアーベル圏 C と同型で閉じた三角部分圏 P に対し、有界 K の全 H^i(K)[0] が P に入れば K も入ることを示す。truncation 三角の HomologySequence から必要な Homology の同型を構成する。

再利用する API は `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`、`singleFunctorCompHomologyFunctorIso`、`TStructure.triangleLEGE`、`DerivedCategory.HomologySequence.exact₁` / `exact₂` / `exact₃` と `ObjectProperty.ext_of_isTriangulatedClosed₂`。上流 `Homology.Perfect.Basic.isPerfect_of_bounded_of_cohomology_isPerfect` の公開 statement は CommRing を仮定するため、非可換 End にそのまま使わない。ここでは任意のアーベル圏で一般的な三角部分圏への所属として検証し、cohomology の perfect 性という別の仮定を隠さない。

`KroneckerPerfect.finite_module_mem` は既存の `rightModuleResolution_shortExact` と `finite_rightModuleResolution_terms` を `ShortComplex.ShortExact.singleTriangle` / `singleTriangle_distinguished`（mathlib `DerivedCategory.SingleTriangle`）へ接続する。これを一般 devissage と合成した `bounded_mem_of_finite_cohomology` は、有限射影加群を含む任意の厳密充満三角部分圏が有界・有限次元コホモロジーの Kronecker 複体も含むことを示す。外部の IsPerfect / IsCompactObject の述語はこの段階で仮定も同定もしていない。

## Kronecker の実際の compact / perfect 判定

`integrations/stacks/KroneckerCompact.lean` は本番 `Beilinson.KroneckerPerfect` と `StacksDraft.Perfect.isPerfect_iff_isCompactObject`（07LT、`Homology.Perfect.Characterizing`）を接続する。任意の非可換環の有限射影加群の single complex を IsPerfect の有限射影代表の定義で構成し、Kronecker の有限次元性と devissage から有界・有限次元コホモロジー⇒compact を得る。逆向きは、perfect 代表の各項が基礎体上有限次元であることと、cycles の包含・homology への全射から示す。`compact_iff_bounded_finite_cohomology` と `perfect_iff_bounded_finite_cohomology` は両方向の判定である。主要宣言は標準の3公理のみを使用し、実 build に成功した。このターゲット自身は幾何学的 End を同定しない。n=1 の同定は後述の `ProjectiveLineEnd` と `ProjectiveLineWindow` で検証した。

このターゲットのため、独立 Stacks project に Root を `../..` の依存として追加した。optional manifest に Root / Verso の固定 dependency が入るが、本番 manifest には Stacks を追加しない。従来の固定 dependency の revision は変更していない。

## 構造層からの Hom と大域切断の線形比較

`integrations/stacks/SheafHomSections.lean` は `bijective_unitHom_app_top_one` を基礎環上の線形同型へ強化する。`unitHomLinearEquiv` は `Scheme.smul_val_app_top` でスカラーとの可換性を証明し、恒等射を1へ送り、対象の射に関して自然である。`unitHomLinearEquivOfLinear` は既に選んだ線形構造と線形な大域切断関手をそのまま使う。`linearOver_eq_modulesLinear` は大域切断とテンソルで用いるスカラー構造が定義的に一致することを確認する。独立ターゲットの実 build と標準3公理の監査に成功した。

本番 `KroneckerEnd.scalarAlgebraEquiv` / `scalarHomEquiv` は、一次元の自己準同型環をスカラーと同定し、恒等射の正規化も証明する。`nonemptyBasisOfFinrank` は正の有限次元から基底の存在を供給する。これらは一般の線形圏・ベクトル空間に関する補題であり、幾何学的 Hom データの代入は別に検証している。

## 射影直線の幾何学的 End

`integrations/stacks/ProjectiveLineEnd.lean` は任意の体上の多項式 Proj P¹ で O(0), O(1) を実際に使う。`unitToTwist_finrank` は Hom(O,O(d)) と大域切断、斉次多項式の比較から d≥0 の次元 d+1 を計算する。O(0)≅O の移送と、線形な捻り自己同値から両対角 Hom の次元1を得る。負捻りの H⁰ の消滅と捻りの忠実性から逆 Hom の消滅を得る。本番 `KroneckerEnd.nonemptyAlgebraEquivOfFinrank` に次元1,1,2と逆 Hom の消滅を渡し、`algebraEquiv` を構成する。基底は選択しており、二本の矢と特定の座標切断の一致は主張しない。`projectiveDimension_le_one` はこの実際の環同型で本番の全右加群の分解を移送する。実 build と標準3公理の監査に成功した。

線形同型のデータを幾何学側で何度も合成するとカーネルで大きな定義展開を生むため、一般の線形圏で次元と零 Hom を移す本番補題 `finrank_hom_map`、`finrank_hom_congr`、`subsingleton_hom_congr` を用いる。検証の制限値は本番の既定値のままである。

## D^b(Coh X) 自体との三角比較

`integrations/stacks/CoherentDerivedComparison.lean` は Tag 0FDB の `coherentToModulesDerivedBoundedEquivalence`（`DerivedCoherent.Modules`）を再利用する。この宣言は標準モデルなので、`modelHomologyFunctorIso`（`SerreSubcategoryModel`）によって有界性と連接性を小さいモデルへ移す `boundedModelEquiv` を作る。`ambientEquivalence` は連接コホモロジーが準連接でもあることを使い、小さいモデルの D_QCoh の中の有界連接部分圏と同定する。Noether スキームについて得る `equivalence` は、D^b(Coh X) 自体を始点とする。

前向き関手を、標準モデルの導来包含とモデル間同値の合成として確認する `coherentCompInclusionIso` を用い、fully faithful な包含との合成が exact であることから exactness を示す。逆方向はシフトを `commShiftInverse` で与え、随伴関手の exactness で導く。小さいモデルの shift / pretriangulated のインスタンスを名前付きで保持し、標準モデルとの暗黙の取り違えを避ける。両方向のシフト・三角保存を含む主要宣言は標準3公理のみを使用し、独立ターゲットの実 build に成功した。Beilinson の compact 始域への有界制限との合成は `BoundedBeilinson` で検証した。

## Kronecker の D^b(有限次元右加群)

本番 `Beilinson/KroneckerFinite.lean` は有限次元ベクトル空間の Serre 性を `Module.Finite.of_injective`、`of_surjective`、`of_exact` で確認し、スカラー制限の逆像として有限次元右 Kronecker 加群の Serre 性を得る。有限次元対象 Y への全射 f に対し、`rightModuleResolution Y` の有限射影項から Y への全射を `Projective.factorThru` で f を通して持ち上げる。`finiteRightModules_coversEpis` は、Serre 部分圏の導来比較に必要な被覆条件そのものである。

独立 `KroneckerBoundedDerived.lean` は `ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory`（Tag 0FCL、`DerivedCategory.SerreSubcategory`）にこの条件を代入する。bounded-above 導来包含の fully faithful 性を有界部分へ制限し、essential image の代表が下からも有界であることをコホモロジーで反映することで、有界版の `equivalence` を得る。`comparisonCompInclusionIso` はこの関手が実際の導来包含であることを記録し、fully faithful な包含を通して exactness を確認する。`KroneckerCompact` と合成した `compactEquivalence` は、実際の D^b(有限次元右加群) と compact 部分圏の同値であり、両方向でシフトと三角を保つ。標準3公理のみを使用し、実 build に成功した。

## 通常 End(E) 右加群からの実際の tensor 同値

`OrdinaryBeilinson.lean` は `endAlgebra_mem_grading_zero`、`endAlgebra_grading_eq_bot`、`endAlgebra_d_eq_zero` を `ConcentratedDGA.comparison` に渡す。幾何学的 dg 代数の基礎環は ℤ なので、現状の adapter は Type 0 の可換環と加群を扱う。逆比較と実際の `tensorWithGenerator` を合成し、`endAlgebraRingEquiv` の反対環でスカラーを変更して、通常の右 End(E) 加群の導来圏からの `endTensor` を得る。これは三角を保つ実際の同値である。

`BoundedBeilinson.lean` は同値による compactness の保存と、射影空間の regular / bounded coherent 判定を合成する。`coherentEquivalence` は任意の次元 n≥0 で compact な通常右 End(E) 加群の部分圏と、実際の D^b(Coh Pⁿ) を三角同値で結び、逆方向の exactness も確認する。有限次元右行列代数加群の有界導来圏への接続は後述の `MatrixBeilinson` で検証した。基礎環上の線形性は `OrdinaryBeilinsonLinear` で別途検証している。

`StacksBeilinsonProbe`、`StacksCohomologyProbe`、`OrdinaryBeilinson`、`BoundedBeilinson` の主要宣言は標準3公理のみを使用し、実 build に成功した。初回の大きなビルドは Stacks の閉包8353モジュールを含み、この4 CPU / 16 GiB 環境では2時間以上を要した。

## 射影直線の有界導来同値の合成

本番 `Beilinson/EndTransport.lean` は対象の同型による End の代数同型、fully faithful な線形関手による End の代数同型、Fin 2 の直和と binary biproduct の同型を与える。

`ProjectiveLineWindow.lean` は O(-1), O(0) の Hom 次元を捻りの線形性で O(0), O(1) の計算へ移す。実際の `twistFamily k 1` の Fin 2 直和を並べ替え、負の窓の `twistSumModule k 1` の End と Kronecker 代数を同定する。正の窓の End との比較はこの基底選択による同型を介し、捻り関手に関する自然同型とはまだ同定していない。

`ProjectiveLineBeilinson.equivalence` の始域は D^b(有限次元右 Kronecker 加群) 自体、終域は多項式 Proj の P¹ 上の D^b(Coh) 自体である。`KroneckerBoundedDerived.compactEquivalence`、実際の End(E) への環変更と導来化、compact 部分圏への制限、`BoundedBeilinson.coherentEquivalence` を合成する。Type 0 の任意の体で前向き・逆向きともシフトと三角を保つ。始域・終域を明記した公開宣言と、別モジュールからの import client を検証した。主要宣言の依存公理は標準3公理のみである。

## 基底選択を使わない正の窓への End 移送

`PositiveWindow.lean` は任意の可換環 k と次元 n に対し、`positiveFamily` を O(0),…,O(n) と定義する。`componentIso` は O(-i)(n)≅O(n-i) を、`generatorIso` は捻り関手の有限直和の保存と `Fin.revPerm` による並べ替えで E(n)≅T を構成する。`endAlgebraEquiv` は `EndTransport.mapEquiv` と対象の同型による移送を合成し、Hom の基底を選ばず End(E)≃ₐEnd(T) を与える。

線形構造には上流の `projectiveSpaceModulesLinear` をそのまま使う。`Scheme.linearOver` と `modulesLinear` の一致を使うときは、暗黙のインスタンス引数を simp で変えるのではなく、データの等式で型を明示的に移送する。対象の同型・線形性・代数同型は実 build と標準3公理の監査に成功した。本番の `EndTransportYoneda` は fully faithful な線形関手と生成対象の同型から、右 End 加群に値を持つ Hom 関手の自然同型を構成する。`PositiveWindow.homFunctorIso` はこれを適用して Hom(E,M)≅Hom(T,M(n)) を実際の右 End(E) 加群として与え、`homComplexFunctorIso` は微分と両立する複体の自然同型を与える。導来 tensor/Hom 関手全体の自然同型はまだ主張しない。

## 中心的係数環と通常加群比較の線形性

`CentralDegreeZero` は、dg 代数の定義上の基礎環 R とは別の可換環 K が中心的な次数0の閉元として作用するとき、局所化・次数成分関手・通常右加群との比較と逆関手が K-線形であることを示す。集中 dg 代数の同一視は基礎環と次数分解を保持して行う。

`OrdinaryBeilinsonLinear` は上流の `scalarRingHom` から実際の幾何学的 dg 環の A-代数構造を構成し、`ordinaryComparison` とその逆、`ordinaryTensor` の A-線形性を確認する。ℤ-線形性だけから基礎体上の有限次元性を主張せず、幾何学的な中心作用との一致を使う。`endAlgebraToEnd_scalar` は dg 環の係数が通常のスカラー自己準同型へ写ることを示し、`endAlgebraEquiv` は環同型を幾何学的基礎環上の代数同型へ強化する。`restrictEnd_linear` と `endTensor_linear` により、環変更後の実際の通常右 End(E) 加群からの tensor 関手も同じ基礎環上で線形となる。有限次元右行列代数加群を始域とする全次元の有界版は、下記の環同型と compactness 判定を使って接続した。

## 全次元の行列代数から実際の有界連接導来圏へ

上流 `StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups` の `Stacks.AlgebraicGeometry.ProjectiveGenerator.matrixRingEquivEnd` は、実際の負捻り和の End を整数次数の同次成分を持つ行列代数と環同型で結ぶ。`GeometricMatrixEnd` では dg 生成対象と同じ負捻り和であることを確認する。数学的に同じ対象でも異なる spelling の End に付随する加法構造は明示して比較する。

`MatrixAlgebraComparison.algebra_eq` は、compactness 判定側の `StacksDraft.Perfect.beilinsonAlgebra` が、幾何学側の `endomorphismMatrices` と同じ部分代数であることを示す。生成集合自体が既に部分代数であり、非負次数の同次性と下三角の零条件が整数次数の同次成分の条件と一致する。`finite_matrix` / `finite_algebra` は各成分の同次多項式空間への単射から有限次元性を得る。

本番 `FiniteModuleCategory.coversEpis` は有限次元代数上の有限次元加群の有限自由被覆を任意の epimorphism を通して持ち上げる。`FiniteBoundedDerived` はこれを Serre 比較定理へ代入する。`bounded_iff_finite_total` は有界性と非零コホモロジー次数の有限性を比較し、既存の行列代数の compactness 判定と接続する。

`MatrixBeilinson.equivalence` の始域は D^b(有限次元右 Beilinson 行列代数加群) 自体、終域は実際の D^b(Coh Pⁿ) 自体であり、Type 0 の任意の体と全ての n≥0 で定式化している。環変更・導来化・compact 部分圏への制限と `BoundedBeilinson.coherentEquivalence` を合成し、両方向のシフトと三角保存を検証した。これは正の窓の導来 tensor/Hom 関手全体との一致をまだ主張しない。

## 実際の正の End(T) 始域と有界導来捻り

`CoherentTensor` は、任意のスキーム上で可逆層との実際の tensor 関手を連接層の圏へ制限する。負の整数 tensor power を使って連接な preimage を構成し、全忠実性と合わせて同値を得る。`ExactBoundedEquivalence` は任意のアーベル圏の完全同値を、選択した導来モデルの実際の有界導来圏の三角同値へ移す。`CoherentTensorBounded.equivalence_functor` は、その前向き関手が実際の制限 tensor 関手の導来化であることを定義的に確認する。

`PositiveBounded.derivedGeneratorIso` は E(n)≅T を実際の D^b(Coh Pⁿ) 内で与える。有限直和の連接性では任意に与えられた `HasBiproduct` を使い、`singleMapIso` は連接層の同型を次数0の有界導来対象へ移す。具体的な射影空間で異なる spelling の single functor を直接比較して膨大な kernel unfolding を起こさず、抽象的な同型の宣言を先に固定する。

`GeometricMatrixLinear.matrix_scalar` は定数対角行列が基礎体のスカラー自己準同型に写ることを行列成分で示す。定数多項式の作用と構造射由来の作用の一致には上流 `TwistEndomorphisms.twistScalar_eq_twistBaseScalar` を使う。本番 `BiproductEnd` の抽象的な成分補題により、具体的 End の加法・スカラー構造の不要な展開を避ける。`positiveAlgebraEquiv` は実際の正の窓の End と Beilinson 行列代数を k-代数同型で結ぶ。

`FiniteScalarEquivalence.coefficientIso` は代数同型による環変更の前後の基礎体上のベクトル空間を明示的に同型にする。単なる環同型だけから有限次元性の保存を仮定しない。実際の有限次元加群の圏の同値を作り、その有界導来圏自体の三角同値へ移す。

`PositiveEndBounded.equivalence` の始域は実際の D^b(有限次元右 End(T) 加群)、終域は実際の D^b(Coh Pⁿ) である。Type 0 の任意の体と全ての n≥0 で、前向き関手・逆向き関手のシフトと三角保存を確認した。始域は構造射由来の正準的な k-代数構造を使い、別モジュールで始域・終域を完全に書いた client も検証した。関手は係数変更、負の窓の tensor 同値、実際の有界導来捻りの合成である。別に古典的に定義する RHom / 導来 tensor との明示的な自然同型は未検証として残す。

## 更新と再現

本番は root `lean-toolchain`, `lakefile.lean` と実生成 `lake-manifest.json` に固定する。Stacks は独立環境で revision を固定し、統合検証に成功した場合にのみ必要な範囲を本番へ移す。上流 63k モジュールの更新に通常の Verso ビルドを従属させない。
