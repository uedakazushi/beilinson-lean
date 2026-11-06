# 研究ノート — 2026-11-07 v0.2

## 数学的な注意点
- P(V) は lines convention、H^0(O(1)) = V^∨。
- 対角線の Koszul 分解の項は O(-r) boxtimes Ω^r(r)。
- Hom(T,-) は右 End(T) 加群。左箙表現と opposite を区別。
- strong exceptional と full の証明は分離する。
- derived Morita はまず Perf(A) の同値。有限次元加群の有界導来圏との同一視は有限大域次元を要する。
- 現行 Book は初稿であり、Čech 複体の単項式ごとの非輪状性、対角線の零点スキームの同定、dg Morita の適用仮定をさらに厳密化する必要がある。

## 実装と再現
- Lean/mathlib/Verso v4.35.0 はタグとして確認したが、統合ビルドは未検証。
- lake-manifest.json は Lake により初めて生成されるまで存在しない。偽の lockfile は作成しない。
- Lean proof は未着手。Beilinson/Foundation.lean は依存性を確認するための skeleton。
- 数学ライブラリと文書は separate Lake targets。MathlibCompat は必要に応じてのみ作成。
