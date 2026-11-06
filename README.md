# Beilinson の定理：射影空間から箙へ

Verso による日本語教科書と Lean 4 形式化を育てるプロジェクトです。生成性の証明は対角線の resolution に依存せず、線束の Koszul 完全列から負捻り線束を作り、SOD の right orthogonal の消滅から示します。

**2026-11-07 / v0.4:** 自然言語による数学的証明は初稿。Beilinson の導来同値の Lean proof はまだありません。依存関係のビルドも未実機検証です。

## 最初に読むもの

1. [PLAN.md](PLAN.md)：研究方針と達成基準
2. [REUSE.md](REUSE.md)：既存形式化の再利用方針・調査台帳
3. [Book.lean](Book.lean) と [Book/](Book/)：Verso の日本語教科書
4. [NOTES.md](NOTES.md)：現在有効な数学的注意点
5. [Beilinson.lean](Beilinson.lean) と [Beilinson/](Beilinson/)：独立した数学ライブラリ（現在 skeleton）
6. [REFERENCES.md](REFERENCES.md)：文献

## 依存関係とビルド

**本番：** Lean 4、mathlib、Verso は v4.35.0 に揃え、root の Lake project に固定。Mathlib の既存 API を最優先して利用する。

```sh
# 依存初回解決時のみ
lake update
# 継続的な検証
bash scripts/check.sh
```

`lake-manifest.json` は実際に Lake が生成したものを本番に commit する。現在は未生成。更新作業以外では意図せず `lake update` をしない。

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
