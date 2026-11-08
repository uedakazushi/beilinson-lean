# Beilinson の定理：射影空間から箙へ

Verso による日本語教科書と Lean 4 形式化を育てるプロジェクトです。生成性の証明は対角線の resolution に依存せず、線束の Koszul 完全列から負捻り線束を作り、SOD の right orthogonal の消滅から示します。

**2026-11-08:** 独立した Stacks 検証環境で、n=1 の具体的 Kronecker 代数の D^b(有限次元右加群) と、実際の D^b(Coh P¹) の三角同値を Lean で検証しました。両方向のシフト・三角保存を確認し、依存公理は標準3公理のみです。この関手は負の捻りの生成対象と基底選択を用います。全ての次元についても、compact な通常右 End(E) 加群から D^b(Coh Pⁿ) への三角同値を検証済みです。現在の通常加群への移送は Lean の Type 0 で定式化しています。

本文の正の捻り T と関手の規約の一致、および一般の次元の有限次元加群の始域を結ぶ部分は未完成です。自然言語の数学的証明は初稿で、本番チェックは Lean ライブラリ・教科書 HTML・LuaLaTeX の日本語 PDF 生成まで成功しています。

## 最初に読むもの

1. [PLAN.md](PLAN.md)：研究方針と達成基準
2. [REUSE.md](REUSE.md)：既存形式化の再利用方針・調査台帳
3. [Book.lean](Book.lean) と [Book/](Book/)：Verso の日本語教科書
4. [NOTES.md](NOTES.md)：現在有効な数学的注意点
5. [Beilinson.lean](Beilinson.lean) と [Beilinson/](Beilinson/)：独立した数学ライブラリ（Kronecker 代数モデル）
6. [REFERENCES.md](REFERENCES.md)：文献

## 依存関係とビルド

Lean 4、mathlib、Verso は v4.35.0 に固定。Verso が直接生成する TeX を LuaLaTeX で組版するため、**Playwright / pypdf / Python は不要**。

**準備（初回）：** LuaLaTeX と、日本語用の `luatexja-fontspec` / HaranoAji 和文フォント、Verso 標準の `memoir`・Source Pro 等の TeX パッケージが必要。Mac ではフルの MacTeX を使うと揃えやすい。

```sh
# mathlib キャッシュ（初回または必要時のみ）
lake exe cache get
# 以降はこれだけで Lean + HTML + PDF をビルド
lake build
```

- HTML：`_out/html-multi/index.html`（`_out/html` が存在しない場合は互換シンボリックリンクも作成）
- Verso が直接生成した TeX：`_out/tex/main.tex`
- 日本語 PDF：`_out/beilinson-book.pdf`（元の `_out/tex/main.pdf` も保持）

`lake build` は Lean ライブラリをビルドし、`generate-book --with-tex` で HTML / TeX を同時生成する。TeX の `memoir` プリアンブルに LuaTeX-ja と HaranoAji フォントの設定を追加して `lualatex` を3回実行する。TeX が生成できない・LuaLaTeX が失敗する場合、`lake build` も失敗する。Python を使った HTML の印刷・PDF 結合は行わない。

`lake-manifest.json` は commit 済み。更新作業以外では意図せず `lake update` をしない。既存の `bash scripts/check.sh` も `lake build` を呼び出す。

**オプション：Axiom Stacks の検証**

`integrations/stacks/` は別 Lake project であり、上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` に固定しています。本番の Verso ビルドには Stacks の依存を追加していません。24個の専用ターゲットで実 import/build と公理監査を行っています。

非有界 dg Beilinson 同値、通常の右 End(E) 加群への比較、compact 部分圏への制限、D^b(Coh Pⁿ) 自体との合成を検証済みです。n=1 では負の窓の End(E) を Kronecker 代数と同定し、実際の D^b(有限次元右加群) を始域とする同値まで合成しました。一般の次元で E(n) と正の窓 T の対象の同型、および捻りによる End 代数の同型も確認しました。関手全体の比較と、基底選択を特定の座標切断へ同定する部分は残っています。詳細と対象ごとの範囲は [検証環境の README](integrations/stacks/README.md) と [再利用台帳](REUSE.md) を参照してください。

```sh
cd integrations/stacks
lake update
lake exe cache get
lake build StacksProbe
lake build StacksGeometryProbe
lake build StacksGenerationProbe
lake build StacksOrdinaryProbe
lake build StacksAlgebraProbe
lake build DGAComparison
lake build DegreeZeroConeComparison
lake build ConcentratedDGA
lake build GeometricPerfectProbe ProjectivePerfectProbe
lake build KroneckerCompact
lake build OrdinaryBeilinson BoundedBeilinson
lake build ProjectiveLineBeilinson
```

README と [REUSE.md](REUSE.md) に記した通り、`StacksCore`（人間レビュー済み）と `StacksFrontier`（kernel-check 済みだが人間レビュー未完了）は区別し、重要な定式化は手動で確認する。

GitHub Actions は使わない。Lean/mathlib/Verso と Stacks の更新は明示的に行い、失敗時には依存関係をむやみに動かさない。

## 検証済みの範囲

`Beilinson/Kronecker.lean` は mathlib の行列部分代数を用い、任意の体上で Kronecker 代数の具体的モデル、4要素の基底、次元4、頂点と矢の積を証明する。幾何学的な自己準同型代数との同定と Beilinson の導来同値は未形式化。`Beilinson/KroneckerModule.lean` は右作用と二本の逆向きの線形写像を相互に構成し、頂点分解による作用の復元、有限次元の場合の次元公式、射の可換条件を証明する。`Beilinson/KroneckerCategory.lean` はこの対応を両方向の関手・自然同型からなる圏同値にまとめ、有限次元対象の充満部分圏にも制限する。`Beilinson/KroneckerResolution.lean` は任意の右加群を終点とする短完全列を構成し、分解の両項の射影性・有限次元性の保存・射影次元が高々1であることを証明する。`Beilinson/KroneckerDimension.lean` は有限次元の非射影単純加群を構成し、射影次元がちょうど1となることを証明する。`Beilinson/KroneckerIdeals.lean` は e₀A・e₁A と標準射影表現の明示的同型、両右イデアルの射影性、正則右加群の分解を証明する。次は幾何学側の既存 API と接続する。

`Beilinson/KroneckerEnd.lean` は一般の k-線形圏の二対象について、対角 Hom のスカラー同定、逆向き Hom の消滅、順向き Hom の二元基底を仮定し、具体的 Kronecker 代数と直和の End の代数同型を構成する。頂点・矢の像と次元4も検証済み。独立した `ProjectiveLineEnd` ターゲットで、実際の射影直線上の O(0), O(1) にこのデータを代入し、End の代数同型と全右加群の射影次元≤1を検証した。同型には二次元 Hom の基底選択を用いる。
`Beilinson/KroneckerYoneda.lean` は Hom(X⊕Y,Z) の二成分への線形同型と、前合成による右作用が二本の逆向き写像と一致することを証明する。標準の右 End 作用を制限した通常の Hom 加群関手と、二頂点の表現から構成した加群関手の自然同型 `homFunctorIso` も検証済み。
`Beilinson/KroneckerEndModules.lean` は環同型に沿って長さ1の射影分解を移送する。上の Hom の仮定を満たす直和の End についても、すべての右加群の射影次元が高々1となる。

`Beilinson/DerivedDevissage.lean` は任意のアーベル圏で、有界対象がそのコホモロジー対象を含む厳密充満な三角部分圏に属することを示す。環の可換性を仮定せず、非可換な代数側でコホモロジーの perfect 性から複体全体へ進むための補題である。

`Beilinson/KroneckerPerfect.lean` は長さ1の有限射影分解を導来圏の三角へ送り、有界かつコホモロジーが有限次元の Kronecker 複体が、有限射影加群を含む任意の厳密充満な三角部分圏に入ることを証明する。外部の perfect / compact という述語への代入は、独立した `integrations/stacks/KroneckerCompact.lean` で検証した。

開発成果は検証後に main へ直接 push する。作業用ブランチや PR は作成しない。

`Beilinson/KroneckerFinite.lean` は有限次元右加群が Serre 部分圏を作ることと、有限射影被覆が任意の全射を通して持ち上がることを証明する。独立した `KroneckerBoundedDerived` ターゲットはこれを導来包含へ適用し、D^b(有限次元右加群) 自体と有界・有限次元コホモロジーの部分圏、さらに compact 部分圏を三角同値で結ぶ。
