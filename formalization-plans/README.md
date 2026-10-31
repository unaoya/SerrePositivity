# 形式化の計画

このディレクトリには、今後の形式化について、対象・証明方針・引用境界・依存関係・完了条件をまとめる。
実装状況の正本は各 Lean モジュールと公理監査であり、計画の記述を証明済みの主張として扱わない。

## ディレクトリ構成

| 場所 | 中身 |
| --- | --- |
| 直下 | 現役の計画（∞ 基盤の整備と Codex 指示書 IF-Wn、R 計画、論文の層の整理計画、Mathlib への提出候補）、全体像、Lean の docstring から参照される案内と棚卸し |
| `bhatt-scholze/` | BS の計画・調査・引き継ぎ、perfectoid 化の界面（E3）の原典照合、Codex 指示書 BS-Wn とその移動計画（JSON）・適用スクリプト |
| `infinity-lanes/` | レーン方式の調整文書（基盤の統合計画 foundations.md と進捗表）と ∞ 系レーン（α・N・D・D2・Ind・P・F1/F2・E2 など）の計画。いずれも完了または R 窓待ちで停止中。再開時の入口 |
| `kst-lanes/` | K 理論の KST 経路の親計画（k-theory-kst-route.md）とレーン別計画（L1〜L11） |
| `future/` | 調査のみ・未着手の将来の計画（Lech、Gersten、Chow 群の経路、arxiv_formalization との共通基盤） |
| `archive/` | 完了した計画、実施記録、役目を終えた指示文・依頼文 |

直下に残る次の文書は Lean の docstring から参照されるので、今はパスを変えない。

| 文書 | 中身 | 参照元と参照の形 | 片づけ方 |
| --- | --- | --- | --- |
| `k-theory.md`（案内。本文は `archive/k-theory-v1.md`） | K 理論 v1 計画（モデル圏の経路、10-15 まで） | HomotopicalAlgebra 約 600・CategoryTheory 約 20・Spectra 1。本文の `[計画書 §396][plan]` と、docstring 末尾の `[plan]: …/k-theory.md` | `[plan]` の定義を `archive/k-theory-v1.md` の §396（「任意モデル源への一般化（中断）」）の見出しへ張り替えて案内を消す |
| `k-theory-generalization-inventory.md`（案内。本文は `archive/` の同名ファイル） | 中断した「任意のモデル源への一般化」の 618 モジュールの棚卸し（分類 A・B・C）と配置整理の実施記録 | HomotopicalAlgebra 約 610・CategoryTheory 約 24。モジュールごとのアンカー `#m0001`〜`#m0618` と「配置実施記録を参照」 | `archive/` の本文の同じアンカーへ張り替えて案内を消す。現状は案内にアンカーがなく、該当行へ直接飛べない |
| `dg-theory-u12e-general-inventory.md` | dg 理論 M5 の単位 U12e の一般版（中断・未受入）の棚卸し：再利用できる API、全モジュール台帳、検証手順、再開条件 | DifferentialGraded 521。「棚卸しと再開条件は…を参照」 | 本文を `archive/` へ移し、参照を張り替える |
| `dg-theory-m5-status.md` | M5（dg 圏の一般論）の完了記録：U0〜U17 の受入表、保留と再開点、M9 への引き継ぎ | DifferentialGraded 9（`Checks/` など）。「受入表からビルド・監査を再現する」 | 本文を `archive/` へ移し、参照を張り替える |

参照元の 1,165 本のうち HomotopicalAlgebra・CategoryTheory の 635 本は [∞ 基盤の整備計画](infinity-foundation-plan.md) の R79 として、W1（全レーン停止の窓）の最初の指示書 IF-W1-1 の冒頭で書き換える。DifferentialGraded の 530 本は [DG の整理計画](dg-cleanup-plan.md) の D5 として、DG の統合（D4）と同じ窓で書き換える（10-30 決定）。いずれも文書ごとに 1 コミット。
docstring だけの変更でも利用先の再ビルドが要るので、それまでは 4 本を動かさない。∞ 側から完了の連絡が来たら、案内 2 本を削除し、この表を片づける。

## 現在地（2026-10-18）

主定理の未証明入力は3件（[公理監査](../scripts/audit_axioms.lean)）。

| 入力 | 原典 | 担当する計画 |
| --- | --- | --- |
| `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` | BS Def 8.2・Lemma 8.4・Prop 8.5・Cor 8.11–8.12・Cor 8.14・Thm 10.11 の E3 界面 | [perfectoid 化の界面](bhatt-scholze/perfectoidization-interface.md)、[∞ 圏](infinity-lanes/infinity-categories.md) §0（G1 達成） |
| `Section4.supportedRankK0_descent` | 論文 補題4.6 | [K理論：KST 経路](kst-lanes/k-theory-kst-route.md) |
| `theorem_3_1_K0` | 論文 定理3.1 | [K理論：KST 経路](kst-lanes/k-theory-kst-route.md) |

外部引用1〜13、BS Cor 7.3・Thm 7.4・Thm 7.14・Lemma 10.3・Remark 10.7、CLMST Prop 2.4.7・Cor 4.0.4 は主定理の経路から外れた。
外部引用の番号と全体の依存関係は [全体像](overview.md) を参照する。

## 進行中の計画

| 計画 | 目標 | 状態 |
| --- | --- | --- |
| [Bhatt–Scholze](bhatt-scholze/bhatt-scholze.md) | BS の引用の現状、原典の依存関係、残る入力の正確な形、原典との経路の差 | B0〜B5・André・Prop 8.13 環版は完了。perfectoid 側の引用は E3 界面の存在 1 件。Thm 1.17(1)・Cor 8.12 の環版は界面から導出済み |
| [BS のリファクタリング](bhatt-scholze/bhatt-scholze-refactoring.md) | 証明済みの BS を共通 API の上に載せ替える | Q10・Q1・Q8 が次の候補（§13） |
| [BS-0 第二段階調査](bhatt-scholze/bhatt-scholze-stage2.md) | E3 の消費経路、A・B・C 案の判定と見積り（2026-10-25） | A 推奨、最初の単位は固定完全 prism 上の affine Čech 模型 |
| [BS 作業チャットへの引き継ぎ](bhatt-scholze/bhatt-scholze-handover-2026-10-25.md) | 文脈・到達点・所有範囲・規約・推奨する進め方 | BS 作業チャットの最初に読む |
| [K理論・スペクトル](k-theory.md) | 定理3.1と補題4.6を形式化し、二つの降下入力を解消する | 段階4（左 Bousfield 局所化と安定モデル）は指定分解版で完了（§397）。M4 以降の経路は下の KST 計画に移行 |
| [K理論：KST 経路と現代的な K](kst-lanes/k-theory-kst-route.md) | KST Thm A（係数つき）＋離散冪零不変性で cdh 降下を得て定理 3.1 を証明し、F5 で補題 4.6 を迂回する。K は安定 ∞ 圏の ∞-S• 構成（dg nerve 経由）、非連結化は dg 側 Schlichting、Sp は γ-B | 2026-10-18 採用。決定事項は §13。L11・L2・L4・L6・L7・L8・L9 を起動 |
| [K理論：任意モデル源への一般化の棚卸し](k-theory-generalization-inventory.md) | 中断した一般化のモジュール索引（docstring からアンカーで参照） | 中断 |
| [P 計画：presentable ∞ 圏](infinity-lanes/infinity-core-presentable.md) | accessible・presentable、随伴関手定理、Bousfield 局所化の存在、P_Σ の普遍性。10-23 新設 | 2026-10-23 |
| [K-7 計画：非連結 K（dg 形）](kst-lanes/L10-nonconnective.md) | Sp の逐次余極限、dg 懸垂と Drinfeld 商、BGT §9。10-23 新設 | 2026-10-23 |
| [∞ 圏基盤の整備計画](infinity-foundation-plan.md) | ∞ 層を KST・DG・EInfinity から自立させ、外の一般論を取り込み、Verdier 商の構成へ進む。段 A〜G、R26〜R70 の要約、決定事項 | 2026-10-28 新設・計画のみ |
| [三つのレーンの調整](coordination.md) | ∞・DG・論文の層の原則（ビルドは減らし同時に走らせない）、ビルドの暦（順番待ち）、いまの待ち条件、調整役の引き継ぎ手順 | 2026-10-31 新設 |
| [DG の整理計画](dg-cleanup-plan.md) | DifferentialGraded/ の検査の処置・入口の新設・層の逆転の解消・1,592 → 126 の統合（D0〜D7）。∞ 基盤とは独立に別の Codex セッションで進める。調査は [archive/dg-survey-2026-10-30.md](archive/dg-survey-2026-10-30.md)、指示書は [DG-W1](dg-codex-w1.md)（完了、取り込み待ち）・[DG-W2](dg-codex-w2.md)（道具と統合の束） | 2026-10-30 新設、10-31 窓割り改訂 |
| [R 計画：∞ 圏基盤のリファクタリング（索引）](refactoring-infinity.md) | リファクタ文書の入口。§0 に R1〜R79 の索引（第 1 窓 R1〜R25 は実施済み、R2 計画 R26〜R47、Verdier 商向け R48〜R57、整備計画 R59〜R79） | 2026-10-28 索引整理 |
| [R 第 2 窓](refactoring-infinity-r2.md)・[Verdier 商向け](refactoring-verdier.md) | R26〜R47・R59〜R67 の調査と候補の詳細、R48〜R57 の配置換えの詳細。順序と窓は infinity-foundation-plan.md §5〜§6 が正本 | 詳細の記録 |
| [論文の層の整理計画](refactor-plan.md) | 論文の層（CategoryTheory・CommutativeAlgebra・HomologicalAlgebra・PerfectComplex・LengthAlgebra・IntersectionMultiplicity・KTheory・Asymptotic・CLMST）の統合・削除・Mathlib への置き換え・層の順序の一本の計画。前半に方針・層の順序・共通の仕組み・段階 0〜3、後半に章ごとの詳細（以前のディレクトリごとの計画書は archive/） | 2026-10-30 一本化 |
| [D2 計画：β4 gluing](infinity-lanes/infinity-core-gluing.md) | dg gluing = lax pullback。10-22 新設の D2 レーン | 2026-10-22 |
| [K-F 計画：K-6 fibration 定理](kst-lanes/L3-fibration.md) | Verdier 列に対する連結 K の fiber 列。10-22 新設の K-F レーン | 2026-10-22 |
| [進捗チェックリスト](infinity-lanes/foundations-progress.md) | foundations.md §9 の本体。レーン別の項目・小項目の完了と日時。コーディネータが進捗確認ごとに更新 | 2026-10-21 分離 |
| [基盤の統合計画](infinity-lanes/foundations.md) | v2（2026-10-19）：基盤優先、K は Land–Tamme（dg 増強流）。∞ 圏・dg 圏・E∞ 代数・K 理論の層の構成、依存関係、現在のレーンとの対応、マイルストーン。基盤全体の正本 | 2026-10-18 採用。α2（F1、[infinity-core-F1.md](infinity-lanes/infinity-core-F1.md)）を新設、α3（F2、[infinity-core-F2.md](infinity-lanes/infinity-core-F2.md)）は α2 の straightening と γ3 の後 |
| [∞ 圏の基盤（α〜ε・Π）](infinity-lanes/infinity-categories.md) | BS §7–§8 と K 理論を quasicategory の基盤に載せる。一旦の目標 G1：perfectoid 化の定義と Cor 8.12 の証明だけを「界面」の存在として保留し、他をすべて証明する | G1 達成（2026-10-18）。E3 の型・二入力への橋・引用の集約と旧公開型での供給は完了。界面の具体的構成と E2 は別工程 |
| [E∞ 代数のモデル圏（レーン E2）](infinity-lanes/e-infinity-algebras.md) | Ch(R) 上の Barratt–Eccles オペラッドの代数のモデル圏（E2a）、その ∞ 圏化 γ（E2b）、BS の続きに要る Tot と単体的可換環（E2c） | 計画。E2a-0（Ch(A) の射影モデル構造）から着手可能（2026-10-18） |
| [dg nerve（∞ 圏基盤 N）](infinity-lanes/dg-nerve.md) | 任意の dg 圏の dg nerve を定義し、quasicategory・H⁰ との比較・pinched 写像空間・関手性を証明する。D(S) := N_dg(Semifree(S)) の前段 | N0〜N6 完了（2026-10-18、571 宣言）。続けて N7（dg の錐が ∞ 極限であること、D4 の核） |
| [D(S)（レーン D）](infinity-lanes/derived-infinity-category.md) | semifree 複体の dg nerve として D(S) を定義し、ホモトピー圏が Mathlib の導来圏と同値であることを証明する | D2・D2f・D1 の定義完了。D2h（cone の閉性、semibasis 表現）を実装中。D1 の quasicategory と D3 は N 完了により着手可能（2026-10-18） |
| [quasicategory の一般論（レーン α）](infinity-lanes/infinity-core.md) | h の橋、join・slice・極限、写像空間と同値、安定 ∞ 圏、完全関手 | A1・A2 完了（2026-10-18）。続けて A3（同値・Joyal の定理・写像空間） |

## 完了した系列の現状

| 系列 | 現状の文書 | 状態 |
| --- | --- | --- |
| dg 理論（M5） | [M5 の完了状況](dg-theory-m5-status.md)、[U12e-general の棚卸し](dg-theory-u12e-general-inventory.md) | 2026-10-17 完了。中心作用・群作用は K 理論の M9 へ。旧 dg-theory.md の内容は M5 の完了状況に統合 |
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
| [dg 理論の主計画（旧）](archive/dg-theory.md) と単位別の記録 `archive/dg-theory-*.md` | 2026-10-17 完了 | [M5 の完了状況](dg-theory-m5-status.md) |
| [BS 主計画（旧）](archive/bhatt-scholze-log.md) | 2026-10-14〜17 の計画と実施記録 | [BS](bhatt-scholze/bhatt-scholze.md)、解説の付録 A |
| [BS：B4 の実行記録](archive/bhatt-scholze-b4-execution.md) | B4 完了（2026-10-16） | 同上 |
| [André の平坦性補題](archive/andre-flatness.md) | Thm 7.14 を証明（2026-10-17） | [BS](bhatt-scholze/bhatt-scholze.md) §4、解説 `par:bs-andre` |
| [完全 F_p 環の Tor 独立性](archive/tor-independence.md) | 完了 | `CommutativeAlgebra/PerfectTorIndependence/Basic.lean` |
| [BS・CLMST の引用解消（旧）](archive/bs-clmst-citation-elimination.md) | 目標 2 まで到達 | [BS](bhatt-scholze/bhatt-scholze.md) §0 |
| [BS リファクタリング（旧版全体）](archive/bhatt-scholze-refactoring-log.md) | §1〜§12 と §13.6 | [リファクタリング](bhatt-scholze/bhatt-scholze-refactoring.md) |

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
