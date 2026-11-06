# Beilinson の定理：射影空間から箙へ

日本語による Beilinson の定理の Verso 教科書と、将来の Lean 4 形式化を収録するプロジェクトです。

**2026-11-07 / v0.2:** 自然言語による証明の初稿がありますが、Beilinson の定理の Lean proof はまだありません。Verso 文書のビルドも未実機検証です。

## 構造

- [PLAN.md](PLAN.md): 現時点の研究方針。再開時には最初に読む。
- [Book.lean](Book.lean) と [Book/](Book/): Verso の自然言語教科書。
- [Beilinson.lean](Beilinson.lean) と [Beilinson/](Beilinson/): mathlib を用いる独立した Lean ライブラリ。現在は依存確認用の空の基盤のみ。
- [NOTES.md](NOTES.md): 現行の数学的注意点・障害。
- [REFERENCES.md](REFERENCES.md): 文献。
- [scripts/check.sh](scripts/check.sh): 手動のビルド検証。GitHub Actions は使用しない。

## 依存関係の方針

Lean 4、mathlib、Verso を **v4.35.0** に統一した。タグの存在および mathlib の toolchain は確認済みだが、三者を組み合わせたビルドは未検証。
`lean-toolchain` と `lakefile.toml` は意図する依存関係を固定する。解決済みの推移的依存関係は **実際に Lake が生成した `lake-manifest.json` を Git で管理する**。現在のリポジトリには manifest がまだない。手書きの偽 manifest は作成しない。

Lean 環境が使えるマシンまたは Cloud Codex で初回のみ次を実行する。

```sh
lake update
lake exe cache get
bash scripts/check.sh
git add lake-manifest.json
git commit -m "Lock resolved Lean dependencies"
git push origin main
```

以降、通常のビルドでは `lake update` を行わず、`bash scripts/check.sh` で独立に数理ライブラリ・教科書・HTML を検査する。

## 長期的な開発規約

- 数学的形式化は `Beilinson/` に置く。Verso の `Book/` は数学的解説と適切な引用のためのもの。
- Lean 定理へのリンクやコード表示は必要になったときに追加する。
- 不安定な mathlib API の利用が繰り返される場合に限り、`Beilinson/MathlibCompat/` に薄い比較補題を作る。予防的な大量ラッパーは作らない。
- 依存パッケージの更新は明示的な作業とし、更新後は数学ライブラリと文書の両方をビルドする。
- GitHub Actions は使わない。
