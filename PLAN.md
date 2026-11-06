# 研究方針 — 2026-11-07 v0.2

## 目的と達成基準
射影空間の導来圏と Beilinson 箙表現の導来圏の同値を、自然言語の証明を備えた Verso 教科書として解説し、続いて Lean 4/mathlib で形式化する。数学的に正確で読める教科書と、依存補題まで含む sorry-free な形式化が最終的な基準。

## 現時点の状態
Book/ に自然言語による初稿を配置。Lean proof は未着手。Beilinson/ に mathlib 依存の形式化用ライブラリを分離して置く。Lean/mathlib/Verso を v4.35.0 タグに揃えた設定を作成したが、Lake の解決とビルドの実機検証はまだ行っていない。生成済みの lake-manifest.json も未登録。Mathlib と Verso の実際の互換性はビルドで確認する必要がある。

## 優先順位
1. Lean 環境で `lake update` して manifest を生成・Git に commit し、`bash scripts/check.sh` を実行する。問題があれば互換バージョンを選定し直す。
2. 自然言語の Čech cohomology、対角線 Koszul 分解、dg Morita の引用定理の仮定を精査して補強する。
3. mathlib の既存 API と証明済み定理を調査する。
4. n=1 の Kronecker 箙・有限次元代数を Lean で構成する。
5. 一般 n の strong exceptional と生成性を形式化する。

## 設計方針
Book/ と Beilinson/ を分離し、同じ Lake プロジェクトで管理する。Lean/mathlib/Verso のバージョンを明示的に合わせ、実際に生成された lake-manifest.json を commit して通常の更新を防ぐ。更新時は library / textbook / HTML を別々に検査する。MathlibCompat は必要になったときだけ追加し、過度に抽象化しない。GitHub Actions は使わない。

## 研究運営の一般原則
数学的重要性・新規性・理解の深化・応用可能性・正確性・実現可能性を総合して研究方針を柔軟に変更する。証明済み・追加仮定に依存・未完成・予想・計算的観察を区別し、本文の数学的証明と Lean kernel の検証を混同しない。先行研究は一次資料を確認し未確認点を明示する。過去の作業履歴ではなく現行の成果を教科書と研究ノートに統合する。bundle には現行の方針・ノート・原稿・再現に必要なソースのみを含め、旧版や中間生成物を含めない。ユーザーの追加承認を求めず研究の区切りごとに Library に保存してよい。ただし Library 内の既存ファイルの削除は明示指示がない限り行わない。生成・検証・GitHub 登録・Library 保存の実施状態を個別に記録する。

## 再開方法
このファイル → Book.lean → Book/ 各章 → NOTES.md → Beilinson/ の順に読む。ビルド方法は README.md と scripts/check.sh を参照。
