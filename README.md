# Beilinson の定理：射影空間から箙へ

Verso による日本語教科書と Lean 4 形式化を育てるプロジェクトです。生成性の証明は対角線の resolution に依存せず、線束の Koszul 完全列から負捻り線束を作り、SOD の right orthogonal の消滅から示します。

**2026-11-07 / v0.4:** 自然言語による数学的証明は初稿。Beilinson の導来同値の Lean proof はまだありません。`n=1` の4次元 Kronecker 代数モデル、右加群圏と逆向きの表現圏の圏同値、および有限次元部分圏への制限は Lean で検証済みです。教科書 HTML の生成について既存の検証報告があります。PDF 経路の実機検証は別途必要です。

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

`integrations/stacks/` は別 Lake project であり、上流 commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` に固定した Stacks の依存を含む。上流の膨大なビルドコストを通常の Verso 文書ビルドへ持ち込まず、再利用する正確な Stacks 定理を選別するためのもの。実機検証はまだ。

```sh
cd integrations/stacks
lake update
lake exe cache get
lake build StacksProbe
```

README と [REUSE.md](REUSE.md) に記した通り、`StacksCore`（人間レビュー済み）と `StacksFrontier`（kernel-check 済みだが人間レビュー未完了）は区別し、重要な定式化は手動で確認する。

GitHub Actions は使わない。Lean/mathlib/Verso と Stacks の更新は明示的に行い、失敗時には依存関係をむやみに動かさない。

## 検証済みの範囲

`Beilinson/Kronecker.lean` は mathlib の行列部分代数を用い、任意の体上で Kronecker 代数の具体的モデル、4要素の基底、次元4、頂点と矢の積を証明する。幾何学的な自己準同型代数との同定と Beilinson の導来同値は未形式化。`Beilinson/KroneckerModule.lean` は右作用と二本の逆向きの線形写像を相互に構成し、頂点分解による作用の復元、有限次元の場合の次元公式、射の可換条件を証明する。`Beilinson/KroneckerCategory.lean` はこの対応を両方向の関手・自然同型からなる圏同値にまとめ、有限次元対象の充満部分圏にも制限する。次は射影加群と長さ1の射影分解を進める。

開発成果は検証後に main へ直接 push する。作業用ブランチや PR は作成しない。
