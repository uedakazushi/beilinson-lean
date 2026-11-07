# Beilinson の定理：射影空間から箙へ

Verso による日本語教科書と Lean 4 形式化を育てるプロジェクトです。生成性の証明は対角線の resolution に依存せず、線束の Koszul 完全列から負捻り線束を作り、SOD の right orthogonal の消滅から示します。

**2026-11-07 / v0.4:** 自然言語による数学的証明は初稿。Beilinson の導来同値の Lean proof はまだありません。`n=1` の4次元 Kronecker 代数モデル、右加群圏と逆向きの表現圏の圏同値、有限次元部分圏への制限、全右加群の長さ1の射影分解と射影次元の上界1と、それを達成する有限次元単純加群は Lean で検証済みです。本番チェックは Lean ライブラリ・教科書 HTML・LuaLaTeX の日本語 PDF 生成まで実機検証済みです。

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

`integrations/stacks/` は別 Lake project であり、上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` に固定する。本番の Verso ビルドには依存を追加していない。例外列の充満性、座標 Koszul の完全性、全負捻りの生成、通常右加群への比較、多項式行列代数の compactness 判定、次数0に集中する dg 代数の比較、cone 規約との符号補正、集中 dg 代数の通常右加群への直接比較を、14個の専用ターゲットで実 import/build・公理監査まで検証した。正則 qcqs スキームでの compactness と有界 coherent コホモロジーの同値、および全ての次元の射影空間への代入も確認した。本番の Kronecker 証明を用いて、右 Kronecker 複体の compactness / perfect 性と有界・有限次元コホモロジーの同値も検証した。構造層からの Hom と大域切断の基礎体上の線形同型、切断とテンソルで使うスカラー構造の一致も確認した。Noether スキームで、D^b(Coh X) 自体と小さい導来圏モデルの有界連接部分圏との三角同値も検証した。詳細は [検証環境の README](integrations/stacks/README.md) を参照。負捻りのコホモロジーと非有界 dg 同値は検証中で、幾何学モデルの接続と本書の有界連接版の主定理は未完成。

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
