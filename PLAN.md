# 研究方針 — 2026-11-07 v0.1

## 目的と達成基準
Verso 教科書に Beilinson の定理の自然言語証明を書き、次に Lean 4/mathlib による完全な形式化へ進む。最終的な達成基準は、全ての依存補題を含む sorry-free な導来同値の Lean theorem と、教育的に自足した教科書。

## 到達点
第1–7章の自然言語証明と第8章の形式化設計を用意した。Lean proof はまだない。第6章の dg Morita と smoothness の諸定理は外部の標準定理に依存する。

## 優先事項
(1) 実機で lake update / lake build / Verso 生成の検査。(2) cohomology の Čech 計算と対角線分解の数学的再検証。(3) mathlib API 調査。(4) n=1 の代数的構成。(5) full exceptional / tilting を一般 n で実装。

## 運営の一般原則
研究価値を最大化するため目標・方針を柔軟に変更する。証明済み、追加仮定依存、未完成、予想、計算観察を区別し、先行研究は一次資料を確認して引用する。現行の成果を自然な順に本文へ統合し、履歴や旧版を蓄積しない。軽量 bundle は現行方針・ノート・教科書・再生成に必要なソースを中心とし、数学内容を削らない。研究の区切りにはユーザーの追加承諾なしに Library 保存を行ってよい。ただし Library 上の旧ファイルの削除は別操作であり、明示指示がなければ行わない。生成・検証・GitHub 登録・Library 保存の状態を混同しない。

## 再開方法
README → PLAN → Book.lean → 各章の順に読む。Lake と Verso のバージョンは lean-toolchain と lakefile.toml に記載。
