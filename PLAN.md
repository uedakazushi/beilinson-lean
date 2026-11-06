# 研究方針 — 2026-11-07 v0.3

## 現時点の目標
自然言語の Beilinson 定理の Verso 教科書を完成させ、既存形式化を最大限再利用して Lean 4 で三角圏同値を形式化する。達成基準は自足的な数学的証明と、主定理・必要な依存補題について sorry-free かつ数学的意味を監査した Lean proof。

## 現在の到達点
Book/ に自然言語による初稿、Beilinson/ に別の Lean library skeleton。root は Lean/mathlib/Verso v4.35.0 へ固定している。Axiom Stacks の公開 source を確認し、同じ Lean/mathlib v4.35.0 に統一されていることを確認した。約 63,000 モジュールでビルドが重いため、本番とは別の `integrations/stacks/` に明示的な upstream commit を固定した実験環境を置いた。root やオプション統合の Lake build、manifest 生成は未検証。Beilinson の数学的形式化は未実施。

## 現在の核心と優先順位
1. 本番 `lake update` で実際の manifest を生成し、`bash scripts/check.sh` で Verso / mathlib の互換性を確認する。
2. Stacks の tagged declarations、mathlib、専門形式化を調査し、REUSE.md の候補を実際の定理名、必要仮定、import と対応づける。巨大 Stacks 全体のコンパイルを最初から必須にしない。
3. 選ばれた少数の Stacks 定理を `integrations/stacks/` で probe し、kernel check と数学的定式化のレビューを分離する。
4. Book/ の Čech、対角線 Koszul、dg Morita の根拠を精査し、定理単位の依存関係を整える。
5. 既存定理で不足する薄い bridge だけを実装し、n=1 から一般 n へ進む。

## 現行の技術方針
Book/ と Beilinson/ を分離した一つの本番 Lake project。Lean/mathlib/Verso の更新は意図的に固定・検証してから行う。Stacks は巨大なので実験用の別 Lake project で調査し、必要な定理と現実的なビルド負担が確認された時点で本番依存を再評価する。既存の定義や定理を無用にコピーしない。REUSE.md を軽量な再利用台帳とし、API/数学的仮定・人間レビュー・ビルド状況を区別する。GitHub Actions は使わない。

## 研究運営の一般原則
数学的重要性・新規性・理解の深化・応用可能性・正確性・実現可能性を総合して方針を柔軟に更新する。証明済み、追加仮定付き、未完成、予想、計算観察を厳密に分け、原稿上の証明と Lean kernel の確認、数学的な statement の監査を区別する。先行研究は一次資料を確認して引用し、確認できない情報を推測しない。現行の教科書と研究ノートへ有効な成果を統合し、更新履歴・旧版・重複ファイルは残さない。研究継続 bundle は現行の方針、研究ノート、教科書と再現に不可欠な最小のソース・依存関係だけで構成し、数学的内容を減らさない。研究の区切りごとに追加承諾を求めず Library 保存してよいが、Library 上の既存ファイルの削除は明示指示がない限り行わない。ファイル生成、検証、GitHub 登録、Library 保存を別々の状態として扱う。

## 再開方法
このファイル → REUSE.md → Book.lean / Book/ → NOTES.md → Beilinson/ → integrations/stacks/README.md の順に読む。
