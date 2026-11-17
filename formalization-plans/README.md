# 形式化の計画

このディレクトリには、今後の形式化について、対象・証明方針・引用境界・依存関係・完了条件をまとめる。
実装状況の正本は各 Lean モジュールと公理監査であり、計画の記述を証明済みの主張として扱わない。
文書の四つの場所（Lean の docstring・`research/`・`blueprint/`・`exposition/`・本ディレクトリ）と参照の向きの規則は [../README.md](../README.md) の「Documents」。本ディレクトリは何を引いてもよいが、ほかの場所は本ディレクトリの中身に事実を頼らない。

## 今の正本（2026-11-17）

| 文書 | 役割 | 最終更新 |
| --- | --- | --- |
| [coordination.md](coordination.md) | レーン・ビルドの規則・暦・各レーンの現状 | 11-17 |
| [stage-ii/stage-ii-second-half.md](stage-ii/stage-ii-second-half.md) | 段階 II 後半の段の表と依存 | 11-14 |
| [coordinator-handover-2026-11.md](coordinator-handover-2026-11.md) | 調整役の引き継ぎ | 11-05 |
| [stage-ii/p0/p0-plan-draft.md](stage-ii/p0/p0-plan-draft.md) | 方針：P⁰（DAG XIII 2.2.6）を第一に、文献に忠実に（P1〜P6） | 11-16 |
| [stage-ii/p0/p0-section-map.md](stage-ii/p0/p0-section-map.md) | P⁰ の地図と項目の閉包の規則 | 11-16 |
| [stage-ii/consolidation/infinity-consolidation-w1.md](stage-ii/consolidation/infinity-consolidation-w1.md) | IC-W1：∞ のコードを InfinityCategories に集める（レーン ⑦） | 11-16 |
| [stage-ii/citation-attributes.md](stage-ii/citation-attributes.md) | `@[cite]`・`@[kerodon]` の規則と略号表 | 11-16 |
| [stage-ii/p0/paper-blueprint.md](stage-ii/p0/paper-blueprint.md) | ブループリント（Verso）の試作の記録 | 11-17 |
| [refactor-ledger.md](refactor-ledger.md) | リファクタ候補の台帳（R・BR、扱いは 閉/B3/計画/保守） | 11-17 |
| [refactor-plan.md](refactor-plan.md) | 論文の層の整理計画（一本化、段階 3 の残り） | 10-30 |
| [bhatt-scholze/design/design-status.md](bhatt-scholze/design/design-status.md) | BS の設計の決定（D 番号） | 11-16 |
| [k-restart-draft.md](k-restart-draft.md) | K の再開の紙の作業 | 11-11 |
| [doc-reorg/README.md](doc-reorg/README.md) | 文書の整理の方針と移動表 | 11-17 |

研究資料の正本：対応表 `../research/<文献>-coverage/`（review の CSV が正本、地図は `map/`）、P⁰ の項目の閉包 `../research/p0-lurie/`、ブループリント `../blueprint/`。

### レーンの指示書と報告

| レーン | 状態（11-17） | 指示書 | 報告 |
| --- | --- | --- | --- |
| ③-a ∞ 供給 a | 5∞-1（S1・S8、外枠 26,000）。choose の全列挙の紙の後に再開 | [stage-ii/inf-supply-w1.md](stage-ii/inf-supply-w1.md) | [stage-ii/report-bs-infinity-a1-stage0.md](stage-ii/report-bs-infinity-a1-stage0.md)、[stage-ii/report-inf-supply-w1.md](stage-ii/report-inf-supply-w1.md)（3b-3 まで） |
| ③-b ∞ 供給 b | OE-W1 段 1（IS-W2 は 3b-4 で停止、D81） | [stage-ii/organize-einfinity-general.md](stage-ii/organize-einfinity-general.md)、[stage-ii/inf-supply-b/inf-supply-w2.md](stage-ii/inf-supply-b/inf-supply-w2.md) | [stage-ii/inf-supply-b/report-inf-supply-w2.md](stage-ii/inf-supply-b/report-inf-supply-w2.md) |
| ⑥ スキーム論 | 2g-2（外枠 23,000）、補題の単位の計画の紙 | [stage-ii/scheme-w1.md](stage-ii/scheme-w1.md) | [stage-ii/scheme-w1-2g-2-report.md](stage-ii/scheme-w1-2g-2-report.md) ほか（停止点の後に `stage-ii/scheme/` へ） |
| 一括（KL-W1 のチャット） | HT04 で停止（main 取り込み済み） | [stage-ii/bulk/bulk-5inf3a.md](stage-ii/bulk/bulk-5inf3a.md)、[stage-ii/bulk/kerodon-layout-w1.md](stage-ii/bulk/kerodon-layout-w1.md) | [stage-ii/bulk/report-bulk-w1.md](stage-ii/bulk/report-bulk-w1.md) |
| ⑤a BS 実装 | 停止（外枠、W16 §404） | [bhatt-scholze/instructions/bhatt-scholze-codex-w16.md](bhatt-scholze/instructions/bhatt-scholze-codex-w16.md) | [bhatt-scholze/reports/report-codex-w16.md](bhatt-scholze/reports/report-codex-w16.md) |
| ⑤d M15・G12 | 停止（G12、ユーザー判断待ち） | [bhatt-scholze/instructions/bhatt-scholze-codex-m15.md](bhatt-scholze/instructions/bhatt-scholze-codex-m15.md) | [bhatt-scholze/reports/report-codex-m15.md](bhatt-scholze/reports/report-codex-m15.md) |
| ⑤a・⑤d の紙 | P⁰ の地図・閉包・DAG/NS・本論文の対応表（済） | [stage-ii/p0/p0-section-map.md](stage-ii/p0/p0-section-map.md) | [stage-ii/p0/](stage-ii/p0/) の report-* |
| ⑦ IC-W1 | 未着手（OE-W1 段 1 の後） | [stage-ii/consolidation/infinity-consolidation-w1.md](stage-ii/consolidation/infinity-consolidation-w1.md) | — |
| ① ∞ 中核 | 止めている（Verdier、K と一緒に後回し） | [stage-ii/consolidation/inf-core-w1.md](stage-ii/consolidation/inf-core-w1.md) | — |

## ディレクトリ構成

| 場所 | 中身 |
| --- | --- |
| 直下 | 正本（上の表）、`overview.md`（全体像）、`mathlib-upstream.md`、`stage-ii-plan-draft.md`（11-05 の段階 II の計画。決定の記録として残す） |
| `stage-ii/` | 段階 II のレーンの指示書と報告。共通の正本は直下、レーンごとに `bulk/`・`p0/`・`inf-supply-b/`・`consolidation/`（③-a と ⑥ の文書は停止点の後に `inf-supply-a/`・`scheme/` へ） |
| `bhatt-scholze/` | BS：`design/`（設計 a0〜a9・design-status・界面）、`instructions/`（BS-Wn・Dn・M15）、`reports/`、`notes/`（調査・引き継ぎ）、`drafts/`（Lean の下書き）。`perfectoidization-interface.md` は Lean の docstring から参照されるので直下のまま |
| `doc-reorg/` | 文書の整理の方針と移動表（`scripts/docs/apply_move_table.py` で適用） |
| `future/` | 調査のみ・未着手の将来の計画 |
| `archive/` | 完了した計画・実施記録・役目を終えた指示文。`archive/stage-i/`：段階 I の計画と `infinity-lanes/`・`kst-lanes/`。`archive/reports/`：レーンの報告の終わった段 |

検証の証拠（json・gz・log、移動表の json、適用スクリプト）は `../evidence/` に移した（11-17）。これからのものは git の外に置き、目録だけをコミットする（`../evidence/README.md`）。

直下に残る次の文書は Lean の docstring から参照されるので、今はパスを変えない。

| 文書 | 中身 | 参照元と参照の形 | 片づけ方 |
| --- | --- | --- | --- |
| `dg-theory-u12e-general-inventory.md`（11-02 に本文を `archive/` へ移動済み。docstring の張り替えは DG-W2(b) の D5） | dg 理論 M5 の単位 U12e の一般版（中断・未受入）の棚卸し：再利用できる API、全モジュール台帳、検証手順、再開条件 | DifferentialGraded 521。「棚卸しと再開条件は…を参照」 | 本文を `archive/` へ移し、参照を張り替える |
| `dg-theory-m5-status.md`（11-02 に本文を `archive/` へ移動済み。張り替えは DG-W2(b) の D5） | M5（dg 圏の一般論）の完了記録：U0〜U17 の受入表、保留と再開点、M9 への引き継ぎ | DifferentialGraded 9（`Checks/` など）。「受入表からビルド・監査を再現する」 | 本文を `archive/` へ移し、参照を張り替える |

HomotopicalAlgebra・CategoryTheory の 635 本が参照していた案内 2 本（`k-theory.md`・`k-theory-generalization-inventory.md`）は、[∞ 基盤の整備計画](archive/stage-i/infinity-foundation-plan.md) の R79 で `archive/k-theory-v1.md`・`archive/k-theory-generalization-inventory.md` へ張り替え（c4290092a・2c8a89952、∞ の束 a12012f0e で main に入った）、2026-11-01 に案内を削除した。残る 2 本（DifferentialGraded の 530 本が参照）は [DG の整理計画](archive/stage-i/dg-cleanup-plan.md) の D5 として、DG の統合（D4）と同じ窓で書き換える（10-30 決定）。docstring だけの変更でも利用先の再ビルドが要るので、それまではこの 2 本を動かさない。

## 現在地（2026-10-18）

主定理の未証明入力は3件（[公理監査](../scripts/audit_axioms.lean)）。

| 入力 | 原典 | 担当する計画 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | BS Def 8.2・Lemma 8.4・Prop 8.5・Cor 8.11–8.12・Cor 8.14・Thm 10.11 の E3 界面 | [perfectoid 化の界面](bhatt-scholze/perfectoidization-interface.md)、[∞ 圏](archive/stage-i/infinity-lanes/infinity-categories.md) §0（G1 達成） |
| `Section4.supportedRankK0_descent` | 論文 補題4.6 | [K理論：KST 経路](archive/stage-i/kst-lanes/k-theory-kst-route.md) |
| `theorem_3_1_K0` | 論文 定理3.1 | [K理論：KST 経路](archive/stage-i/kst-lanes/k-theory-kst-route.md) |

外部引用1〜13、BS Cor 7.3・Thm 7.4・Thm 7.14・Lemma 10.3・Remark 10.7、CLMST Prop 2.4.7・Cor 4.0.4 は主定理の経路から外れた。
外部引用の番号と全体の依存関係は [全体像](overview.md) を参照する。

## 進行中の計画

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [Bhatt–Scholze](bhatt-scholze/notes/bhatt-scholze.md) | BS の引用の現状、原典の依存関係、残る入力の正確な形、原典との経路の差 | B0〜B5・André・Prop 8.13 環版は完了。perfectoid 側の引用は E3 界面の存在 1 件。Thm 1.17(1)・Cor 8.12 の環版は界面から導出済み |
| [BS のリファクタリング](bhatt-scholze/notes/bhatt-scholze-refactoring.md) | 証明済みの BS を共通 API の上に載せ替える | Q10・Q1・Q8 が次の候補（§13） |
| [BS-0 第二段階調査](bhatt-scholze/notes/bhatt-scholze-stage2.md) | E3 の消費経路、A・B・C 案の判定と見積り（2026-10-25） | A 推奨、最初の単位は固定完全 prism 上の affine Čech 模型 |
| [BS 作業チャットへの引き継ぎ](bhatt-scholze/notes/bhatt-scholze-handover-2026-10-25.md) | 文脈・到達点・所有範囲・規約・推奨する進め方 | BS 作業チャットの最初に読む |
| [K理論・スペクトル（v1、アーカイブ）](archive/k-theory-v1.md) | 定理3.1と補題4.6を形式化し、二つの降下入力を解消する | 段階4（左 Bousfield 局所化と安定モデル）は指定分解版で完了（§397）。M4 以降の経路は下の KST 計画に移行 |
| [K理論：KST 経路と現代的な K](archive/stage-i/kst-lanes/k-theory-kst-route.md) | KST Thm A（係数つき）＋離散冪零不変性で cdh 降下を得て定理 3.1 を証明し、F5 で補題 4.6 を迂回する。K は安定 ∞ 圏の ∞-S• 構成（dg nerve 経由）、非連結化は dg 側 Schlichting、Sp は γ-B | 2026-10-18 採用。決定事項は §13。L11・L2・L4・L6・L7・L8・L9 を起動 |
| [K理論：任意モデル源への一般化の棚卸し（アーカイブ）](archive/k-theory-generalization-inventory.md) | 中断した一般化のモジュール索引（docstring からアンカーで参照） | 中断 |
| [P 計画：presentable ∞ 圏](archive/stage-i/infinity-lanes/infinity-core-presentable.md) | accessible・presentable、随伴関手定理、Bousfield 局所化の存在、P_Σ の普遍性。10-23 新設 | 2026-10-23 |
| [K-7 計画：非連結 K（dg 形）](archive/stage-i/kst-lanes/L10-nonconnective.md) | Sp の逐次余極限、dg 懸垂と Drinfeld 商、BGT §9。10-23 新設 | 2026-10-23 |
| [∞ 圏基盤の整備計画](archive/stage-i/infinity-foundation-plan.md) | ∞ 層を KST・DG・EInfinity から自立させ、外の一般論を取り込み、Verdier 商の構成へ進む。段 A〜G、R26〜R70 の要約、決定事項 | 2026-10-28 新設・計画のみ |
| [IF-W0-4](archive/infinity-codex-w0-4.md)・[IF-W2a-2](archive/infinity-codex-w2a-2.md) | ∞ 側の次の指示書：基盤の層（CategoryTheory の一般部分・Coxeter）の登録と verify runner のメモリ予算つき並列化／R76・R77・R67 の一束 | 2026-11-01 作成、開始は束の後 |
| [三つのレーンの調整](coordination.md) | ∞・DG・論文の層の原則（ビルドは減らし同時に走らせない）、ビルドの暦（順番待ち）、いまの待ち条件、調整役の引き継ぎ手順 | 2026-10-31 新設 |
| [DG の整理計画](archive/stage-i/dg-cleanup-plan.md) | DifferentialGraded/ の検査の処置・入口の新設・層の逆転の解消・1,592 → 126 の統合（D0〜D7）。∞ 基盤とは独立に別の Codex セッションで進める。調査は [archive/dg-survey-2026-10-30.md](archive/dg-survey-2026-10-30.md)、指示書は [DG-W1](archive/dg-codex-w1.md)（完了）・[DG-W2](archive/dg-codex-w2.md)（完了）・[DG-W3](archive/dg-codex-w3.md)（土台の統合、1-4 の後） | 2026-10-30 新設、10-31 窓割り改訂 |
| [R 計画：∞ 圏基盤のリファクタリング（索引）](archive/stage-i/refactoring-infinity.md) | リファクタ文書の入口。§0 に R1〜R79 の索引（第 1 窓 R1〜R25 は実施済み、R2 計画 R26〜R47、Verdier 商向け R48〜R57、整備計画 R59〜R79） | 2026-10-28 索引整理 |
| [R 第 2 窓](archive/stage-i/refactoring-infinity-r2.md)・[Verdier 商向け](archive/stage-i/refactoring-verdier.md) | R26〜R47・R59〜R67 の調査と候補の詳細、R48〜R57 の配置換えの詳細。順序と窓は infinity-foundation-plan.md §5〜§6 が正本 | 詳細の記録 |
| [論文の層の整理計画](refactor-plan.md) | 論文の層（CategoryTheory・CommutativeAlgebra・HomologicalAlgebra・PerfectComplex・LengthAlgebra・IntersectionMultiplicity・KTheory・Asymptotic・CLMST）の統合・削除・Mathlib への置き換え・層の順序の一本の計画。前半に方針・層の順序・共通の仕組み・段階 0〜3、後半に章ごとの詳細（以前のディレクトリごとの計画書は archive/） | 2026-10-30 一本化 |
| [D2 計画：β4 gluing](archive/stage-i/infinity-lanes/infinity-core-gluing.md) | dg gluing = lax pullback。10-22 新設の D2 レーン | 2026-10-22 |
| [K-F 計画：K-6 fibration 定理](archive/stage-i/kst-lanes/L3-fibration.md) | Verdier 列に対する連結 K の fiber 列。10-22 新設の K-F レーン | 2026-10-22 |
| [進捗チェックリスト](archive/stage-i/infinity-lanes/foundations-progress.md) | foundations.md §9 の本体。レーン別の項目・小項目の完了と日時。コーディネータが進捗確認ごとに更新 | 2026-10-21 分離 |
| [基盤の統合計画](archive/stage-i/infinity-lanes/foundations.md) | v2（2026-10-19）：基盤優先、K は Land–Tamme（dg 増強流）。∞ 圏・dg 圏・E∞ 代数・K 理論の層の構成、依存関係、現在のレーンとの対応、マイルストーン。基盤全体の正本 | 2026-10-18 採用。α2（F1、[infinity-core-F1.md](archive/stage-i/infinity-lanes/infinity-core-F1.md)）を新設、α3（F2、[infinity-core-F2.md](archive/stage-i/infinity-lanes/infinity-core-F2.md)）は α2 の straightening と γ3 の後 |
| [∞ 圏の基盤（α〜ε・Π）](archive/stage-i/infinity-lanes/infinity-categories.md) | BS §7–§8 と K 理論を quasicategory の基盤に載せる。一旦の目標 G1：perfectoid 化の定義と Cor 8.12 の証明だけを「界面」の存在として保留し、他をすべて証明する | G1 達成（2026-10-18）。E3 の型・二入力への橋・引用の集約と旧公開型での供給は完了。界面の具体的構成と E2 は別工程 |
| [E∞ 代数のモデル圏（レーン E2）](archive/stage-i/infinity-lanes/e-infinity-algebras.md) | Ch(R) 上の Barratt–Eccles オペラッドの代数のモデル圏（E2a）、その ∞ 圏化 γ（E2b）、BS の続きに要る Tot と単体的可換環（E2c） | 計画。E2a-0（Ch(A) の射影モデル構造）から着手可能（2026-10-18） |
| [dg nerve（∞ 圏基盤 N）](archive/stage-i/infinity-lanes/dg-nerve.md) | 任意の dg 圏の dg nerve を定義し、quasicategory・H⁰ との比較・pinched 写像空間・関手性を証明する。D(S) := N_dg(Semifree(S)) の前段 | N0〜N6 完了（2026-10-18、571 宣言）。続けて N7（dg の錐が ∞ 極限であること、D4 の核） |
| [D(S)（レーン D）](archive/stage-i/infinity-lanes/derived-infinity-category.md) | semifree 複体の dg nerve として D(S) を定義し、ホモトピー圏が Mathlib の導来圏と同値であることを証明する | D2・D2f・D1 の定義完了。D2h（cone の閉性、semibasis 表現）を実装中。D1 の quasicategory と D3 は N 完了により着手可能（2026-10-18） |
| [quasicategory の一般論（レーン α）](archive/stage-i/infinity-lanes/infinity-core.md) | h の橋、join・slice・極限、写像空間と同値、安定 ∞ 圏、完全関手 | A1・A2 完了（2026-10-18）。続けて A3（同値・Joyal の定理・写像空間） |

## 完了した系列の現状

| 系列 | 現状の文書 | 状態 |
| --- | --- | --- |
| dg 理論（M5） | [M5 の完了状況](archive/dg-theory-m5-status.md)、[U12e-general の棚卸し](archive/dg-theory-u12e-general-inventory.md) | 2026-10-17 完了。中心作用・群作用は K 理論の M9 へ。旧 dg-theory.md の内容は M5 の完了状況に統合 |
| CLMST | [当時の計画と実施記録](archive/clmst.md) | 2026-10-17 完了。数学は解説と `SerrePositivity/CLMST/` の docstring |

## 調査・計画のみ

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [全体像](overview.md) | 外部引用の番号・役割・依存関係の一覧 | 2026-10-18 に現状へ更新 |
| [外部引用5：Chow 群の基盤と Roberts の経路](future/intersection-vanishing-cycles.md) | Chow 群・局所 Chern 指標・局所 Riemann–Roch。BlochConjecture と共有 | 計画のみ。引用5は Adams の経路で解消済みで、これとは独立 |
| [Lech の重複度予想](future/lech.md) | Lech の論文の定理1.1 | 設計段階 |
| [Gersten 予想の整数係数の反例](future/gersten.md) | OpenAI の二本（K₃ と K₅）を K 理論の基盤の上で形式化する | 計画のみ |
| [arxiv_formalization との共通基盤](future/shared-foundations-arxiv.md) | 群論・モノイダル圏論の部分の共通化の検討 | 検討課題の記録のみ |

## アーカイブ（`archive/`）

完了した計画と、役目を終えた調査・補助の文書。数学の内容は解説（`exposition/ja/exposition-ja.tex`）と
Lean の docstring へ要約済みで、各ファイルの冒頭に要約先を記した。将来は削除する予定。

| 計画 | 結果 | 要約先 |
| --- | --- | --- |
| [外部引用1〜3：環の存在構成](archive/local-algebra-1-3.md) | 引用1・2・3を実構成へ置換（2026-10-14） | 解説の付録 A、補題 2.1・2.2 |
| [Cohen–Gabber の微分経路](archive/cohen-gabber-differentials.md) | 引用2を証明（2026-10-14） | 解説の補題 2.2 |
| [完備化の共通基盤と二つの適用](archive/adic-completion-integration.md) | 引用1・3の解消に使用 | 共通の完備化 API の docstring |
| [外部引用4〜5：交点重複度](archive/intersection-inputs-4-5.md) | 当初の経路比較。4・5とも解消 | 解説の付録 A、注意 `rem:adams-vanishing` |
| [外部引用4を主定理から外す（対角線論法）](archive/serre-equal-characteristic.md) | 完了（2026-10-14） | 解説の付録 A、`IntersectionMultiplicity/Diagonal*` |
| [外部引用5：消滅定理を Adams 作用素で](archive/intersection-vanishing-adams.md) | 完了（2026-10-15） | 解説の注意 `rem:adams-vanishing` |
| [外部引用6を主定理から外す（初等版）](archive/frobenius-koszul-elementary.md) | 完了（2026-10-14） | 解説の注意 `rem:koszul-elementary` |
| [Frobenius 高次ホモロジー消滅（一般形）](archive/frobenius-homology.md) | 主定理・Lech の主定理とも不要。一般形は Lech の系 5.4 だけ | `Inputs/RobertsFrobenius.lean` |
| [BS：B3 の実行計画](archive/bhatt-scholze-b3-execution.md) | B3（Cor 7.3 の存在・普遍性）完了 | 解説の付録 A（`par:bs-thm74`）、`BhattScholze/` の docstring |
| [BS：Prop 7.2 の接続設計](archive/bhatt-scholze-prop72-construction.md) | 実装済み | 同上 |
| [BS：F3 受領後の実装順](archive/bhatt-scholze-f3-next.md) | 完了 | 同上 |
| [CLMST の長さの引用監査](archive/clmst-length-audit.md) | 監査済み（2026-10-13） | 解説、`SerrePositivity/CLMST/` |
| [CLMST の実装境界と作業単位](archive/clmst-interfaces.md) | 初回の接続実装まで完了 | 同上 |
| [CLMST 主計画（旧）](archive/clmst.md) | 2026-10-17 完了 | 同上 |
| [dg 理論の主計画（旧）](archive/dg-theory.md) と単位別の記録 `archive/dg-theory-*.md` | 2026-10-17 完了 | [M5 の完了状況](archive/dg-theory-m5-status.md) |
| [BS 主計画（旧）](archive/bhatt-scholze-log.md) | 2026-10-14〜17 の計画と実施記録 | [BS](bhatt-scholze/notes/bhatt-scholze.md)、解説の付録 A |
| [BS：B4 の実行記録](archive/bhatt-scholze-b4-execution.md) | B4 完了（2026-10-16） | 同上 |
| [André の平坦性補題](archive/andre-flatness.md) | Thm 7.14 を証明（2026-10-17） | [BS](bhatt-scholze/notes/bhatt-scholze.md) §4、解説 `par:bs-andre` |
| [完全 F_p 環の Tor 独立性](archive/tor-independence.md) | 完了 | `CommutativeAlgebra/PerfectTorIndependence/Basic.lean` |
| [BS・CLMST の引用解消（旧）](archive/bs-clmst-citation-elimination.md) | 目標 2 まで到達 | [BS](bhatt-scholze/notes/bhatt-scholze.md) §0 |
| [BS リファクタリング（旧版全体）](archive/bhatt-scholze-refactoring-log.md) | §1〜§12 と §13.6 | [リファクタリング](bhatt-scholze/notes/bhatt-scholze-refactoring.md) |

## 運用

リポジトリ全体の現状は [README](../README.md)、論文と実装の対応は
[日本語解説](../exposition/ja/exposition-ja.tex)、現在の未証明依存は
[公理監査](../scripts/audit_axioms.lean)を参照する。

### 置き場所の原則

| 情報 | 置き場所 |
| --- | --- |
| 数学の内容（主張・証明の方針） | 解説と Lean の docstring |
| 現状（済み・残り） | この README の表と、各計画の冒頭の「現在地」 |
| 計画（目標、方針、決定事項とその理由、残りの工程と受入条件） | 各計画の本文。数百行に保つ |
| 実施記録（いつ何をし、どう検証したか） | 計画には書かず、コミットメッセージに書く |
| 引用 | `Inputs` の docstring |
| 検討ノート | `research/` |

### 書き方

- 新しい計画には、作成日、対象とする版、最終目標、段階ごとの成果物、引用として残す結果を記載する。
- 状態が変わったら本文の「現在地」を書き換える（追記しない）。方針を変えたら、変更と理由を本文に明記する。
- 実施記録を本文へ追記しない。過去の記録は `archive/` に置き、要約先がそろったら削除する。
