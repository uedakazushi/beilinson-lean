# Beilinson の定理：射影空間から箙へ

Lean 4 / Verso による日本語教科書プロジェクトです。まず自然言語で数学的証明を書き、その後 Lean proof を段階的に追加します。**現在は自然言語の証明であり、Lean による Beilinson 定理の形式化は未着手です。**

## 読む順序

まず [PLAN.md](PLAN.md) を読み、続いて [Book.lean](Book.lean) と [Book/](Book/) の各章を参照してください。研究上の注意点は [NOTES.md](NOTES.md)、文献は [REFERENCES.md](REFERENCES.md)。

## 構築

公式 Verso basic-book の構成に合わせています。Lean toolchain は v4.36.0-rc2 に固定。

```sh
lake update
lake build
lake exe generate-book
lake exe verso-serve
```

これは実行手順であり、このリポジトリでは **まだビルドの実機検証を行っていません**。GitHub Actions は設定していません。
