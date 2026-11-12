# ∞ 圏の勉強ノートの R 番号と形式化の側の記録の照合（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。基準：main ba24dceb6。読み取りだけのエージェント 1 本で調べ、食い違いのうち R62・R50・R53 は作成者が grep で確かめた。

- 目的：形式化の調整役への受け渡し。ユーザーの方針（11-12）で、リファクタ候補はノートでなく形式化の側で管理し、扱いは調整役が判断する。**ここには事実だけを書く。**
- BS（`research/bs-refactor-audit/`）との違い：∞ の R 番号は、形式化の側にすでに索引がある（`formalization-plans/refactoring-infinity.md` §0、R1〜R79 の正本の所在）。ノートに出る 49 個（＋R49a・R49b・R56a・R61a・R61b）はすべて形式化の側の文書に番号で載っている。だから受け渡すのは「ノートにしかない内容」と「食い違い」だけ。
- ノートの側の予定：調整役が必要な内容を形式化の側に取り込んだ後、`exposition/ja/infinity/` の赤い囲み（33 個）と本文・表の中の R の記述を外す（または台帳への参照にする）。囲みの原文は `box-texts.md`。
- 略号：ri＝refactoring-infinity.md（最終更新 10-30）、r2＝refactoring-infinity-r2.md（10-28）、rv＝refactoring-verdier.md（10-28）、ifp＝infinity-foundation-plan.md（11-05）。ノートの日付は各章の基準コミット：00〜08 章・route-yoneda 10-23（R58 は 10-28 改番）、route-classification 10-24、k-nonconnective-design 10-27、f-00〜f-05 10-28。

## 1. 全体の事実

- ノートは R1〜R25 を「候補」とだけ書き、f-* の表は「移動予定」と書く。実施の結果を書き戻した箇所はない。
- ri §0 の索引も 10-30 のまま（「W0 進行中」）。KL-W1（11-12）でディレクトリが Kerodon/・HTT/・HA/・Project/ に変わったが、R 文書のパス（Stable/Verdier、F1B/Localization など）は旧い構成のまま。
- 中身が正本と同じで、ノートにしかない内容のないもの：R2（候補の R2 として）、R3、R7、R11〜R17、R19、R20、R22〜R26、R32、R33、R37〜R39、R48、R49、R55、R57、R59、R65、R66、R68、R71、R56a。

## 2. ノートにしかない内容

| R | ノートの所在 | ノートだけにある内容 | 正本の記録 |
| --- | --- | --- | --- |
| R1 | 00-map §5 | 主題別ディレクトリの具体案、F1↔F1B の import 64・119 回 | ri §0.1「実施済み」。ただし ifp は 10-28「改名は後」、11-04「改名しない」。KL-W1 で配置は変わったが R1 としての記録はない |
| R4 | 00-map | 「公開の主定理と途中の補題を分ける」中身、平均 70 行 | ri §0.1「先送り（ファイル粒度）」の語だけ |
| R5 後半 | 01 章 | 双対化の対象の具体例と行数（TerminalUniqueness 249・InitialUniqueness 230、JoinLifting、RelativeOuterHorn/Op 各 202） | ri 1-5、前半は 10-23 実施、後半は先送り |
| R6 | 01・03 章 | Core/Cocartesian*・RelativeOuterHorn* をディレクトリとして移す案 | ri 1-4・4-3 は入口ファイルの作成まで（実際に移ったかは未確認） |
| R8 | 02・08 章、**r8-duplication.html** | 宣言単位の数値（同一本体 275 群、余分なコピー 364 個・約 3,400 行、KanSection 139 宣言中 126 が同一）、コピーの作成日時（10-18・10-19）、根本原因の説明（所有権と依存禁止の規則が重なると逃げ道がコピーしかない）、準重複の組 2 件（F1↔F2 JoinRightRelativeExtension 0.86、KanCoconeApexTransport↔CoconeCartesianTransport 0.92）、リスク（open PinchedInterval での名前の曖昧化など） | ri §4・§7、重複一覧 archive/refactor-duplicates-2026-10-23.md（基準が違い 18 群） |
| R9 | 02 章 | MappingSpace/ にまとめる案 | ri 1-4 は入口ファイルまで、ifp の目標構成に「Core/ 写像空間（PinchedHom を吸収）」 |
| R10 | 02 章 | 対象の述語（IsSimplicialHomotopyEquivalence・IsQCatEquivalence・IsPrecompositionEquivalence）と、計算規則を別々に証明しているファイル（EquivalenceCalculus ほか 3 本） | ri §0.1「先送り（計算規則の統合）」の語だけ |
| R18 の三つ目 | 05 章 | kanDiagramCoherentNerve が F1 にある | ri 段 5 は前の二つ（docstring、名前）だけ |
| R21 | 06 章 | docstring の書式を守る割合（F2 27%、F2/Ind 0%、1,630 個中 1,547 個が一行文、HL 31%、F1 49%） | ri §0.1 先送り |
| R27（別の意味） | route-classification:450 | 写像空間の模型 3（Fun(Δ¹,C) の fiber）を定義として加え、pinched 模型との同値を示す案 | formalization-plans にない（research/kerodon-coverage は未確認） |
| R54（別の意味） | f-01:145 | KanHomotopyGroup X n が π_{n+1} を表す添字の名前の見直し | R 文書にない。正本の R54 は名前空間の付け替え（F-2、11-05） |
| R58 | route-yoneda §6・§7 | Yoneda の閉包（約 1,750 本に KST.Spectra 8・Stable 43・HA 167）と二つの最短経路の形、fibration 版 Yoneda の閉包 256 本が R8 の汚染経路を通ること | ri §0 は所在としてノートを指す。経路の辺は archive/r2-a-layers（140・153・63 行）と r2-survey |
| R72 | f-02 §7、f-01:103 | モデル圏依存の原因分析の具体例（Generators→Transfer.EvaluationSmallness の未使用 import）、三つ目の原因「ディレクトリの置き場所」、UniverseLiftModel・WeakEquivalence の扱い | ifp §3・段 C、W2a・W2c 群 A′ |

## 3. 正本の記録と今のコードの食い違い（ノートとは別に、正本の側で見つかったもの）

- **R50**：ifp 段 B・§9-4 は「束ねない形 IsVerdierPair（仮名）と同値補題を新設」。IF-W1W2a の行には「w1.json の中身」とあるが、w1.json に R50 の項目はなく、コードに `IsVerdierPair` はない（作成者が grep で確認）。実施・取りやめのどちらの記録もない。
- **R52**：ノートは「Stable/Verdier/Fractions へ一括」。実際は W2c 群 B（11-04）で Stable・StablePresentable・Derived の三か所に分かれ、保留 98 本は w2c-stage-g-input.json。`fraction_ho_localization` は KST に残る（R52 の対象のうち未完）。
- **R53**：ifp 段 B は retractClosure の移動と IsThick・thickClosure の定義。W1 は retractClosure だけ、IF-W2c で「R53 は段 G」。`IsThick`・`thickClosure` はコードにない（作成者が確認）。
- **R62**：ifp 段 A は `fraction_ho_localization` の公開（1h）、w1.md では「W1 の手作業」。今も `KST/LocalizingInvariants/VerdierFractionComparison.lean:44` に `private lemma` のまま（作成者が確認）。実施・取りやめのどちらの記録もない。
- **R64**：f-01:227 は「計画 §9 で置き場所を確認」と書くが、ifp §9 には該当がない（ifp §3 の 10-28 決定「Kan・pointed は InfinityCategories の中」が対応すると推測）。
- **R72**：f-02（10-28）は「HA の 12 本を分割すればモデル圏の依存は消える」。正本（11-04）では HA 66・ModelBridge 8 本が残り、段 G の M16（CosliceTwistedHomEquivalence が Reedy の定理を使う、cleanup-list L3）。

## 4. 番号の食い違い

- **R27**：route-classification（10-24）の R27 は模型 3 の案、r2（10-27）の R27 は HL・F1→KST.Spectra。同じ番号で中身が違い、改番の記録がない。
- **R54**：上の §2 のとおり、ノートは名前の見直しにも使う。
- **R26→R58**：10-28 に改番済み（ri §0 と route-yoneda の両方に記録）。
- **R3**：ノートの R3 は HL→KST.Spectra を含むが、正本ではその部分が R27 に分かれた（範囲の分割）。
- **「R2 計画」**：route-yoneda と k-nonconnective の「R2 計画」は第 2 窓の計画（r2）で、候補の R2 とは別物。

## 5. ノートから外すと切れる参照

- ri §0 の R58 の行と「候補の出所」の行が `exposition/ja/infinity/route-yoneda.html` と `r8-duplication.html` を指す。
- ifp の M8 と `stage-ii/inf-core-w1.md:25` が「解説 第 5 章 §5」（f-05-verdier-quotient.html の §5「商の関手性（M8）」、数学の内容）を指す。これは R の囲みではないので外さない。

## 6. 追記（11-12 夜）：f-00〜f-05 の表の所在を引き直したときに分かったこと（事実だけ）

ノートの表を「今の所在」に作り替えるため、各行の代表的な宣言を main 95c8f5c8c で引き直した（114 宣言の file:line を確認）。そのときに分かった、計画の記述と今のコードの違い：

- **Ω による安定性の判定（HA Cor 1.4.2.27）**：ノートと計画では「未着手（D-7）」だったが、`isStable_of_loopEquivalence`（`InfinityCategories/HA/StableInfinityCategories/LoopEquivalenceStability.lean:20`）がある。このファイルに sorry はない（依存先は未確認）。
- **局所化の延長の二つの版**（旧 R61a）：`localization_extension_exists`（`InfinityCategories/Project/HomotopyDiagramComparison/LocalizationExtension.lean:25`、EInfinity/FrameHom から移動）と `IsLocalization.exists_extension`（`InfinityCategories/Kerodon/AdjointFunctors/Localization/UniversalConsequences.lean:36`）が両方ある。
- **KST・EInfinity・HomotopicalAlgebra に残っている ∞ の一般論**：
  - `KST/Spectra`：Tower* 26 本、`kanPiIsomorphism_of_anodyne`、based path と Ω の fiber 表示（`pointedEndpointLoop_isPullback`）
  - `KST/SConstruction`：Necklace* 45 本
  - `KST/LocalizingInvariants`：`laxCategory`、`fraction_ho_localization`（private）
  - `KST/Fibration`：Verdier 分数の大半
  - `EInfinity/SimplicialLocalization`：`modelHammock_isLocalization`、`hammockLocalizationNerveMap`
  - `HomotopicalAlgebra/Simplicial`：Kan 置換・KanTestDetection・Diagonal*。モデル圏を使うのは 16 本（UniverseLiftWeakEquivalence・UniverseLiftModel・Diagonal{Cofibrations,Quillen,LocalizedEquivalence,Anodyne} など）
- `InfinityCategories/Kerodon/KanComplexes/HomotopyGroups/PointedKanWhitehead.lean` に、空の `namespace SerrePositivity.KST.Spectra` が残っていて、それを open している。
- 同じ名前の `pinchedHom` が `Kerodon/TheHomotopyTheoryOfInfinityCategories/MorphismSpaces` の Basic.lean（SSet 版）と PinchedHom.lean（dg 版）にあり、名前空間で分かれている。
- 改名表 `scripts/refactor/targets/kl-module-map.json` は InfinityCategories と KST の一部（Comparison・ProExcision・LocalizingInvariants・SConstruction）だけを持ち、KST/Spectra・EInfinity・HomotopicalAlgebra は対象外。
- ノートで「HA/Simplicial」「HA/Generated」と書いていたのは `HomotopicalAlgebra/` のこと。KL-W1 でできた `InfinityCategories/HA/`（Higher Algebra）とは別物。
