# 形式化の計画

このディレクトリには、今後の形式化について、対象・証明方針・引用境界・依存関係・完了条件をまとめる。
実装状況の正本は各 Lean モジュールと公理監査であり、計画の記述を証明済みの主張として扱わない。

## 現在地（2026-10-16）

主定理の未証明入力は5件（[公理監査](../scripts/audit_axioms.lean)）。

| 入力 | 原典 | 担当する計画 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidization_of_integral` | BS Thm 1.17(1) | [BS](bhatt-scholze.md)、[引用解消の計画](bs-clmst-citation-elimination.md) |
| `CLMST.Inputs.corollary_4_0_4` | CLMST Cor 4.0.4 | [CLMST](clmst.md)（KL系列） |
| `CLMST.Inputs.proposition_2_4_7` | CLMST Prop 2.4.7 | [CLMST](clmst.md)（D系列） |
| `Section4.supportedRankK0_descent` | 論文 補題4.6 | [K理論](k-theory.md) |
| `theorem_3_1_K0` | 論文 定理3.1 | [K理論](k-theory.md) |

外部引用1〜7・12・13、BS Cor 7.3／Thm 7.4 は主定理の経路から外れた。
外部引用の番号と全体の依存関係は [全体像](overview.md) を参照する。

## 進行中の計画

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [CLMST とその準備](clmst.md) | CLMST の結果を原典の形で述べ、定理2.5への接続と Prop 2.4.7・Cor 4.0.4 の証明を進める | G系列（BSへの共通API）は完了。KL（Cor 4.0.4）を実装中、その後D（Prop 2.4.7）。BSとの分担・作業順は§0.2 |
| [Bhatt–Scholze：δ環と prism から perfectoid 化へ](bhatt-scholze.md) | δ環・prism を基礎から形式化し、BS の引用を解消する | B0〜B4 完了。Thm 7.4 の全射性は André の補題を使わない経路で証明し、引用を解消。Thm 1.17(1) は引用のまま |
| [BS の実行計画（B4）](../SerrePositivity/BhattScholze/B4ExecutionPlan.md) | B4 の各工程の実施記録 | B4 完了。ソースディレクトリ内にあるが、参照元が多いため現在は移動しない |
| [BS のリファクタリング](bhatt-scholze-refactoring.md) | 証明済みの BS を共通 API の上に載せ替える | 実施中。現在の正本は§13 |
| [BS・CLMST の引用解消](bs-clmst-citation-elimination.md) | 発表時に残す引用を BS の命題だけにする作業順 | 計画のみ。CLMST の G2 合流後に着手 |
| [K理論・スペクトル・dg 理論](k-theory.md) | 定理3.1と補題4.6を形式化し、二つの降下入力を解消する | 段階4（一般の左 Bousfield 局所化と安定モデル）は F1 の最終厳密化を残してほぼ完了。M4・M6〜M10 は未着手 |
| [dg 理論（M5）](dg-theory.md) | dg 圏・dg 加群・perfect・dg 商・Morita を独立に実装する | U0〜U12 完了。U13（perfect）と U15（dg 商）を実装中 |

## 完了した計画

| 計画 | 目標 | 結果 |
| --- | --- | --- |
| [外部引用1〜3：環の存在構成](local-algebra-1-3.md) | 剰余体拡大・Cohen／Cohen–Gabber 正規化 | 引用1・2・3を実構成へ置換（2026-10-14） |
| [Cohen–Gabber の微分経路](cohen-gabber-differentials.md) | p-basis・係数体・連続微分から引用2を証明する | 完了（2026-10-14） |
| [完備化の共通基盤と二つの適用](adic-completion-integration.md) | 共通のテンソル比較・完備化の平坦性と、CLMST／剰余体拡大への適用 | 引用1の解消に使用。実施記録として保持 |
| [外部引用4を主定理から外す（対角線論法）](serre-equal-characteristic.md) | 剰余標数零の場合を Serre の対角線論法で証明する | 完了（2026-10-14）。主定理は引用4に依存しない |
| [外部引用5：消滅定理を Adams 作用素で](intersection-vanishing-adams.md) | 巡回 Adams 作用素と重みで `intersectionVanishing` を証明する | 完了（2026-10-15）。S1〜S11 |
| [外部引用6を主定理から外す（初等版）](frobenius-koszul-elementary.md) | パラメータ Koszul 複体の場合を tight closure なしで証明する | 完了（2026-10-14）。主定理は引用6に依存しない |
| [CLMST の長さの引用監査](clmst-length-audit.md) | C1/C2 の仮定と利用先の調査 | 監査済み（2026-10-13） |
| [CLMST の実装境界と作業単位](clmst-interfaces.md) | 型と引用の境界、共通層の抽出順 | 初回の接続実装まで完了。以後は [CLMST 主計画](clmst.md) で管理 |

## 調査・計画のみ

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [全体像](overview.md) | 外部引用の番号・役割・依存関係の一覧 | 2026-10-16 に現状へ更新 |
| [外部引用4〜5：交点重複度](intersection-inputs-4-5.md) | 4・5 の証明経路の比較 | 当初の調査。4・5とも上の計画で解消済み |
| [外部引用5：Chow 群の基盤と Roberts の経路](intersection-vanishing-cycles.md) | Chow 群・局所 Chern 指標・局所 Riemann–Roch。BlochConjecture と共有 | 計画のみ。Adams の経路とは独立 |
| [Frobenius 高次ホモロジー消滅（一般形）](frobenius-homology.md) | 引用6の一般形の証明経路 | 調査段階。主定理は既に依存しない |
| [Lech の重複度予想](lech.md) | Lech の論文の定理1.1 | 設計段階 |
| [Gersten 予想の整数係数の反例](gersten.md) | OpenAI の二本（K₃ と K₅）を K 理論の基盤の上で形式化する | 計画のみ |
| [arxiv_formalization との共通基盤](shared-foundations-arxiv.md) | 群論・モノイダル圏論の部分の共通化の検討 | 検討課題の記録のみ |

## 運用

リポジトリ全体の現状は [README](../README.md)、論文と実装の対応は
[日本語解説](../exposition/ja/exposition-ja.tex)、現在の未証明依存は
[公理監査](../scripts/audit_axioms.lean)を参照する。

新しい計画には、作成日、対象とする版、最終目標、段階ごとの成果物、引用として残す結果を記載する。
過去の会話の仮案と現在採用する方針が異なる場合、その変更を本文に明記する。

CLMSTとBSの今後の共通基盤・作業順・受入条件は[CLMST主計画§0.2](clmst.md)を参照する。
BS原典の証明経路は[BS計画](bhatt-scholze.md)を正本とする。

### 長い計画の分割方針（未実施）

k-theory.md・bhatt-scholze.md・clmst.md・dg-theory.md・B4ExecutionPlan.md は、
冒頭の計画と後半の実施記録が一体になり、数千〜一万行を超えている。
各作業が区切りに達して追記が止まった時点で、次の形へ分ける。

- 本文：目標、採用方針、現在地、残りの工程と受入条件。数百行程度に保つ。
- 実施記録：日付ごとの実装・検証の記録を `archive/` 以下へ移す。本文から節番号で参照する。

並行作業中に分割すると追記と衝突するため、各担当が作業を止めたときに行う。
B4ExecutionPlan.md の formalization-plans/ への移動も、そのときに合わせて行う。
