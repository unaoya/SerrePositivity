# 形式化の計画

このディレクトリには、今後の形式化について、対象・証明方針・引用境界・依存関係・完了条件をまとめる。
実装状況の正本は各 Lean モジュールと公理監査であり、計画の記述を証明済みの主張として扱わない。

## 現在地（2026-10-18）

主定理の未証明入力は3件（[公理監査](../scripts/audit_axioms.lean)）。

| 入力 | 原典 | 担当する計画 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | BS Def 8.2・Lemma 8.4・Prop 8.5・Cor 8.11–8.12・Cor 8.14・Thm 10.11 の E3 界面 | [perfectoid 化の界面](perfectoidization-interface.md)、[∞ 圏](infinity-categories.md) §0（G1 達成） |
| `Section4.supportedRankK0_descent` | 論文 補題4.6 | [K理論](k-theory.md) |
| `theorem_3_1_K0` | 論文 定理3.1 | [K理論](k-theory.md) |

外部引用1〜13、BS Cor 7.3・Thm 7.4・Thm 7.14・Lemma 10.3・Remark 10.7、CLMST Prop 2.4.7・Cor 4.0.4 は主定理の経路から外れた。
外部引用の番号と全体の依存関係は [全体像](overview.md) を参照する。

## 進行中の計画

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [Bhatt–Scholze](bhatt-scholze.md) | BS の引用の現状、原典の依存関係、残る入力の正確な形、原典との経路の差 | B0〜B5・André・Prop 8.13 環版は完了。perfectoid 側の引用は E3 界面の存在 1 件。Thm 1.17(1)・Cor 8.12 の環版は界面から導出済み |
| [BS のリファクタリング](bhatt-scholze-refactoring.md) | 証明済みの BS を共通 API の上に載せ替える | Q10・Q1・Q8 が次の候補（§13） |
| [K理論・スペクトル](k-theory.md) | 定理3.1と補題4.6を形式化し、二つの降下入力を解消する | 段階4（左 Bousfield 局所化と安定モデル）は指定分解版で完了（§397）。M4 以降の経路は下の KST 計画に移行 |
| [K理論：KST 経路と現代的な K](k-theory-kst-route.md) | KST Thm A（係数つき）＋離散冪零不変性で cdh 降下を得て定理 3.1 を証明し、F5 で補題 4.6 を迂回する。K は安定 ∞ 圏の ∞-S• 構成（dg nerve 経由）、非連結化は dg 側 Schlichting、Sp は γ-B | 2026-10-18 採用。決定事項は §13。L11・L2・L4・L6・L7・L8・L9 を起動 |
| [K理論：任意モデル源への一般化の棚卸し](k-theory-generalization-inventory.md) | 中断した一般化のモジュール索引（docstring からアンカーで参照） | 中断 |
| [Stage 4 の依存監査](stage4-dependency-audit.md) | 指定分解版に限った段階4の依存の監査 | 2026-10-17 監査 |
| [P 計画：presentable ∞ 圏](infinity-core-presentable.md) | accessible・presentable、随伴関手定理、Bousfield 局所化の存在、P_Σ の普遍性。10-23 新設 | 2026-10-23 |
| [K-7 計画：非連結 K（dg 形）](kst-lanes/L10-nonconnective.md) | Sp の逐次余極限、dg 懸垂と Drinfeld 商、BGT §9。10-23 新設 | 2026-10-23 |
| [新設指示 10-23](restart-2026-10-23.md) | P・K-7 の指示文と転用の予告 | 2026-10-23 |
| [再開指示 10-24（v3、8 レーン）](restart-2026-10-24.md) | リファクタ後の仕切り直し。Ind・P・D・D2・E2・Sp・K-S•・K-B の再開文と共通規約 | 2026-10-24 |
| [R 計画：∞ 圏基盤のリファクタリング](refactoring-infinity.md) | 解説の候補 R1〜R25 を互換シム方式で段階実施。重複除去、層の整理、逆向き依存の解消。10-23 新設 | 2026-10-23 |
| [D2 計画：β4 gluing](infinity-core-gluing.md) | dg gluing = lax pullback。10-22 新設の D2 レーン | 2026-10-22 |
| [K-F 計画：K-6 fibration 定理](kst-lanes/L3-fibration.md) | Verdier 列に対する連結 K の fiber 列。10-22 新設の K-F レーン | 2026-10-22 |
| [再開・新設指示 10-22](restart-2026-10-22.md) | F1・N の方針変更と D2・K-F の新設の指示文 | 2026-10-22 |
| [進捗チェックリスト](foundations-progress.md) | foundations.md §9 の本体。レーン別の項目・小項目の完了と日時。コーディネータが進捗確認ごとに更新 | 2026-10-21 分離 |
| [基盤の統合計画](foundations.md) | v2（2026-10-19）：基盤優先、K は Land–Tamme（dg 増強流）。∞ 圏・dg 圏・E∞ 代数・K 理論の層の構成、依存関係、現在のレーンとの対応、マイルストーン。基盤全体の正本 | 2026-10-18 採用。α2（F1、[infinity-core-F1.md](infinity-core-F1.md)）を新設、α3（F2、[infinity-core-F2.md](infinity-core-F2.md)）は α2 の straightening と γ3 の後 |
| [∞ 圏の基盤（α〜ε・Π）](infinity-categories.md) | BS §7–§8 と K 理論を quasicategory の基盤に載せる。一旦の目標 G1：perfectoid 化の定義と Cor 8.12 の証明だけを「界面」の存在として保留し、他をすべて証明する | G1 達成（2026-10-18）。E3 の型・二入力への橋・引用の集約と旧公開型での供給は完了。界面の具体的構成と E2 は別工程 |
| [E∞ 代数のモデル圏（レーン E2）](e-infinity-algebras.md) | Ch(R) 上の Barratt–Eccles オペラッドの代数のモデル圏（E2a）、その ∞ 圏化 γ（E2b）、BS の続きに要る Tot と単体的可換環（E2c） | 計画。E2a-0（Ch(A) の射影モデル構造）から着手可能（2026-10-18） |
| [dg nerve（∞ 圏基盤 N）](dg-nerve.md) | 任意の dg 圏の dg nerve を定義し、quasicategory・H⁰ との比較・pinched 写像空間・関手性を証明する。D(S) := N_dg(Semifree(S)) の前段 | N0〜N6 完了（2026-10-18、571 宣言）。続けて N7（dg の錐が ∞ 極限であること、D4 の核） |
| [D(S)（レーン D）](derived-infinity-category.md) | semifree 複体の dg nerve として D(S) を定義し、ホモトピー圏が Mathlib の導来圏と同値であることを証明する | D2・D2f・D1 の定義完了。D2h（cone の閉性、semibasis 表現）を実装中。D1 の quasicategory と D3 は N 完了により着手可能（2026-10-18） |
| [quasicategory の一般論（レーン α）](infinity-core.md) | h の橋、join・slice・極限、写像空間と同値、安定 ∞ 圏、完全関手 | A1・A2 完了（2026-10-18）。続けて A3（同値・Joyal の定理・写像空間） |

## 完了した系列の現状

| 系列 | 現状の文書 | 状態 |
| --- | --- | --- |
| dg 理論（M5） | [M5 の完了状況](dg-theory-m5-status.md)、[U12e-general の棚卸し](dg-theory-u12e-general-inventory.md) | 2026-10-17 完了。中心作用・群作用は K 理論の M9 へ。[dg-theory.md](dg-theory.md) は案内のみ |
| CLMST | [CLMST](clmst.md)（案内のみ） | 2026-10-17 完了。数学は解説と `SerrePositivity/CLMST/` の docstring |

## 調査・計画のみ

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [全体像](overview.md) | 外部引用の番号・役割・依存関係の一覧 | 2026-10-18 に現状へ更新 |
| [外部引用5：Chow 群の基盤と Roberts の経路](intersection-vanishing-cycles.md) | Chow 群・局所 Chern 指標・局所 Riemann–Roch。BlochConjecture と共有 | 計画のみ。引用5は Adams の経路で解消済みで、これとは独立 |
| [Lech の重複度予想](lech.md) | Lech の論文の定理1.1 | 設計段階 |
| [Gersten 予想の整数係数の反例](gersten.md) | OpenAI の二本（K₃ と K₅）を K 理論の基盤の上で形式化する | 計画のみ |
| [arxiv_formalization との共通基盤](shared-foundations-arxiv.md) | 群論・モノイダル圏論の部分の共通化の検討 | 検討課題の記録のみ |

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
| [dg 理論の主計画（旧）](archive/dg-theory.md) と単位別の記録 `archive/dg-theory-*.md` | 2026-10-17 完了 | [M5 の完了状況](dg-theory-m5-status.md) |
| [BS 主計画（旧）](archive/bhatt-scholze-log.md) | 2026-10-14〜17 の計画と実施記録 | [BS](bhatt-scholze.md)、解説の付録 A |
| [BS：B4 の実行記録](archive/bhatt-scholze-b4-execution.md) | B4 完了（2026-10-16） | 同上 |
| [André の平坦性補題](archive/andre-flatness.md) | Thm 7.14 を証明（2026-10-17） | [BS](bhatt-scholze.md) §4、解説 `par:bs-andre` |
| [完全 F_p 環の Tor 独立性](archive/tor-independence.md) | 完了 | `CommutativeAlgebra/PerfectTorIndependence/Basic.lean` |
| [BS・CLMST の引用解消（旧）](archive/bs-clmst-citation-elimination.md) | 目標 2 まで到達 | [BS](bhatt-scholze.md) §0 |
| [BS リファクタリング（旧版全体）](archive/bhatt-scholze-refactoring-log.md) | §1〜§12 と §13.6 | [リファクタリング](bhatt-scholze-refactoring.md) |

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

### 長い計画の分割（未実施）

k-theory.md（約2.3万行）と ∞ 圏の系列は、計画と実施記録が一体になっている。
各担当が区切りに達して追記が止まった時点で、本文（数百行）と `archive/` の記録に分ける。
k-theory.md の §396・§397 と k-theory-generalization-inventory.md・dg-theory-u12e-general-inventory.md の
アンカーは多数の docstring から参照されるので、パスと節番号を変えない。
