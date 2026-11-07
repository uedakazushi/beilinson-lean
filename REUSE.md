# 既存形式化の再利用方針 — 2026-11-08 v0.5

## 原則

**実装する前に既存の Lean 定義・補題・定理を調べる。** 順序は (1) 現在 pinned された mathlib、(2) Axiom StacksCore、(3) Axiom StacksFrontier、(4) 他の専門的形式化プロジェクト、(5) 不足する橋渡し補題を新規実装、である。この順序は品質監査の優先順であり、数学的に最適な構成が別なら変更してよい。

他プロジェクトの定理を使えるかどうかは、**単に似た名前があるか**では判断しない。Lean の正確な statement、仮定、型の互換性、定義の意味、依存する axiom、実際の import/build を確認する。探す場所と候補を調査した段階は「実装済み」ではない。

## Axiom Stacks の実情

2026-11-06 の上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` は Lean 4.35.0、mathlib v4.35.0 で、本プロジェクトとバージョンが合う。プロジェクトには約 63,000 モジュールがあり、上流 README も大規模なコンパイル時間・メモリ消費を注意している。

- **StacksCore**: 人間によるレビュー済み。優先して利用。
- **StacksFrontier**: AI 生成・Lean kernel による形式的証明は存在するが、人間による忠実性のレビューは未完了。重要な橋渡し定理では原文の Stacks tag・定式化・仮定を数学的に再確認する。
- `@[stacks TAG]` / `#stacks_tags` と https://stacks.axiommath.ai/ は tag → Lean declaration → import の探索に使う。タグが Mathlib に登録されている場合は Mathlib の定理を優先。

通常の book/Lean ビルドに Stacks 全体を import しない。実験用環境 `integrations/stacks/` は **別 Lake project** で上流を正確な commit に固定しており、通常ビルドの軽さを保つ。これは将来の proof の本番使用を妨げるものではないが、本番での Stacks 依存には再検討・adapter が必要である。例外生成列・Koszul の二つの実験 probe は実 import/build に成功し、コホモロジー probe は検証中。

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
| exceptional collections / tilting | StacksFrontier、Axiom BondalThomsen | Koszul 生成性・非有界 dg 同値の正確な宣言を確認。追加 probe を検証中 |
| dg enhancement / derived Morita | StacksFrontier | `Beilinson.beilinson_equivalence` は非有界 dg 加群と準連接導来圏の同値。ソース照合済み、ローカル検証中。有界・連接版との比較は未実装 |
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
- `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic`、import `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange`。基底 scheme S、n=m+1≥1、-n≤d<0、q∈ℤ について R^q f_* O(d)=0。Tag [01XW](https://stacks.math.columbia.edu/tag/01XW) の各行の既存結果を合成する定理で、この宣言自身への tag 属性はない。`StacksCohomologyProbe` で検証中（閉包2125モジュール）。

重要な型の境界：Koszul は多項式 Proj、higher direct image は整数上の射影空間を基底変換したモデルを使う。両者の同一視はまだ adapter に含めていない。`TwistGenerator.Negative` は自明化開集合上の線束の生成切断であり、導来圏の右直交零検出を直接述べる定理ではない。Ext/cohomology 比較、有限 total Hom、Koszul から全負捻りへの伝播と Serre による零検出、導来 Morita は未完成。

検証済み二つの adapter の依存公理は `propext`、`Classical.choice`、`Quot.sound` のみ。root の production dependency は変更しない。専用 manifest を `integrations/stacks/` に保存する。

## 深い階層で確認した生成性・dg 同値の候補

以下は正確なソースと証明経路を確認した結果。宣言ごとにローカル build 状態を区別する。

- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul` の `Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen`。多項式 Proj 上で E=O⊕O(-1)⊕…⊕O(-n) とし、全ての m≥0 で O(-m) が `gen E` に属する。証明は座標 Koszul の stupid filtration による有限 cone と強い帰納法で、対角線の分解を使わない。閉包228モジュール。`StacksGenerationProbe.negative_twist_generated` と `negative_twist_orthogonal` の実 import/build・公理監査に成功。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.KoszulQuasiCoherent` の `isWeakTriangulatedGenerator_twistSumDerivedQCoh`（同 namespace、Tag [0A9V](https://stacks.math.columbia.edu/tag/0A9V)）。Koszul 生成性と ample 負捻りの零検出を多項式 Proj 上で接続する。この経路なら基底変換モデルのコホモロジーとの比較を経ず生成性を進められる。閉包2378モジュール、単独の検証は未実施。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEquivalenceLinear` の `Stacks.AlgebraicGeometry.Beilinson.beilinson_equivalence`（Tag [0BQU](https://stacks.math.columbia.edu/tag/0BQU)）。任意の可換環 A と n≥0 に対し、上記 E の dg 自己準同型代数 R からの derived tensor が D(R) と D_QCoh の A-線形三角同値を与え、正則加群を E に送る。定理の仮定に同値性自体は含まれない。ソースは生成性、compactness、正則加群間の Hom の同型から導く。閉包8353モジュール。`StacksBeilinsonProbe` を検証中。
- import `StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.BeilinsonEndAlgebra` の `Stacks.AlgebraicGeometry.Beilinson.endAlgebraRingEquiv`、`endAlgebra_d_eq_zero`、`endAlgebra_grading_eq_bot` は R が通常の End(E) に集中することを述べる。既存の `DifferentialGradedModule.degreeZeroDerivedEquivalence`（import `StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra`）は degree-zero DGA の右加群を通常の反対環の加群の複体へ比較する。`StacksOrdinaryProbe.rightModuleComparison` と `rightModuleComparison_exact` で、任意の非可換 R-代数 S の degree-zero DGA から Sᵐᵒᵖ の加群の導来圏への同値と三角の保存を検証済み。上流と同じ局所 pretriangulated instance を明示する必要があった。依存公理は標準の3つのみ。ただし幾何学側の DGA と degree-zero DGA の universe・基礎環の型を接続する adapter は未実装。

- import `StacksFrontier.Homology.Perfect.BeilinsonAlgebra` の `StacksDraft.Perfect.hasFiniteTotalCohomology_iff_isCompactObject` は、多項式の斉次成分から作る上三角行列 Beilinson 代数の右加群の導来圏で、compactness と有限 total cohomology の同値を述べる。閉包96モジュール。`StacksAlgebraProbe.compact_iff_finite_total_cohomology` の実 import/build と公理監査に成功。依存公理は標準の3つのみ。幾何学的 End との同型はこの定理に含まれない。

教科書の T=O⊕O(1)⊕…⊕O(n) は上記 E を O(n) で捻り、直和を逆順に並べたもの。従って数学的には対応するが、その自然同型・自己準同型代数・右加群規約と bounded coherent / finite-dimensional 制限を Lean で移送する部分は別の課題である。非有界 dg 版の既存定理を、そのまま本書の完成した主定理とは呼ばない。

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

`algebraEquiv` の追加仮定は、Hom(X,X)≃ₗ[k]k と Hom(Y,Y)≃ₗ[k]k（各恒等射を1へ送る）、Subsingleton Hom(Y,X)、および Hom(X,Y) の Fin 2 基底。4成分の座標抽出と再構成を示して全単射性を証明し、`ofArrows` の乗法保存で代数同型へ昇格する。`ofArrows_e₀`、`ofArrows_e₁`、`ofArrows_arrow` は生成元の像を射影・包含と選んだ射として確認し、`finiteDimensional` と `finrank` は条件付き End の有限次元性と次元4を与える。幾何学的 Hom の仮定は未代入であり、End(O⊕O(1)) の具体的同定が完成したとは扱わない。

再利用した pinned mathlib API：`Biprod.ofComponents`、`Biprod.ofComponents_comp`、`Biprod.ofComponents_eq`（`Mathlib.CategoryTheory.Preadditive.Biproducts`）、`CategoryTheory.End` とその `asHom` / `of`、`Module.Basis.sum_repr`、`AlgHom.ofLinearMap`、`AlgEquiv.ofLinearEquiv`。End は Hom の単なる略記ではないため、morphism の計算へは `asHom` で移す。主要宣言の実 build と公理監査に成功し、依存は標準の3公理のみ。

ライブラリ入口は `module` / `public import` を使い、新しい module クライアントからの公開 API を確認する。空の Foundation の Mathlib umbrella import は最小限の category import へ整理し、数学ファイルが個別の依存を持つ。

## 標準の Hom 右作用と射影分解への接続

`Beilinson/KroneckerYoneda.lean` の `homFunctor` は mathlib の `preadditiveCoyonedaObj (X⊞Y)` と、`ofArrows` の反対環準同型に沿う `ModuleCat.restrictScalars` の合成である。独自に作用を置いて標準の End 作用との一致を仮定していない。`homCoordinates_precompose` は二成分への線形分解が `Kronecker.ofArrows` の作用を保つことを示す。`homModuleEquiv` は通常の反対代数加群の線形同型で、`homFunctorIso` は二つの Hom を頂点に持つ `representationFunctor` と `fromReverseRep` の合成への自然同型である。

`Beilinson/KroneckerEndModules.lean` は任意の環同型 A≃S に対して `restrictScalarsEquivalenceOfRingEquiv` を使う。`resolution` の短完全性は `ShortExact.map_of_exact`、両項の射影性は `Equivalence.map_projective_iff` で移送し、`resolutionTargetIso` で終点を元の加群に戻す。`projectiveDimension_le_one` と条件付きの `end_projectiveDimension_le_one` はこの実際の短完全列から得る。これらも本番の build と標準3公理の監査に成功した。

## 幾何学側の compactness と有界 coherent の接続

`GeometricPerfectProbe.compact_iff_boundedCoherent` は、qcqs な正則スキーム X に対して、locally small な D_QCoh の compact 対象と有界 coherent コホモロジーを持つ対象を同定する。前半は `Stacks.Duality.QcqsPerfect.isCompactObject_iff_isPerfect`（09M1、`AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsCompactIsPerfect`）、後半は `Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular`（0FDC、`…Perfect.RegularBoundedCoherentPerfect`）。二つの perfect の定義は Scheme の RingedSpace.{u,u} で定義上同じであることを確認した。derived-category model は `Scheme.Modules.hasDerivedCategory` に揃える。

`ProjectivePerfectProbe.regular` は `…Variety.Projective.RegularProjectiveSpace` の `ProjPolyChart.isRegularLocalRing_stalk_proj` と `…ProjNoetherian.Basic` の Noetherian 性を `AlgebraicGeometry.isRegular_tfae` で組み合わせる。`compact_iff_boundedCoherent` は任意の体、全ての n≥0 の多項式 Proj への代入である。両ターゲットの実 build と標準3公理の監査に成功した。

これは幾何学側の対象条件の確認である。Beilinson 関手の制限、代数側の有限次元条件、Db(Coh) 自体と D_QCoh 内の有界 coherent 対象の比較は別に必要である。

## 更新と再現

本番は root `lean-toolchain`, `lakefile.lean` と実生成 `lake-manifest.json` に固定する。Stacks は独立環境で revision を固定し、統合検証に成功した場合にのみ必要な範囲を本番へ移す。上流 63k モジュールの更新に通常の Verso ビルドを従属させない。
