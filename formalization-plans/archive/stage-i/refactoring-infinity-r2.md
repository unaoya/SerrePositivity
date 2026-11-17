# R 第 2 窓：事前調査と計画検証（2026-10-27 新設）

概要：第 I 段の I-5・I-6 完了後に実施する R 第 2 窓（候補 R26〜）の事前調査を、稼働レーンを止めずに並列・読み取り専用で行う。
方針：第 1 窓（R1〜R25、[refactoring-infinity.md](refactoring-infinity.md)）と同じ運用——候補を番号付けし、全レーン停止窓で
`scripts/move_module.py` と `scripts/refactor/verify.sh`（全体ビルド・全監査・sorry 閉包）で実施する。調査はコードを変更しない。
規約：候補は「対象モジュール・移動先または統合先・影響する利用元の本数・検証方法・工数」を一行で記録する。数学的内容・公開名・型は保存する。
使われ方：調査結果は本ファイル §2〜§4 に集約し、R 第 2 窓の実施順と担当を決める。自動調査の付録は
[archive/r2-survey-2026-10-27.md](../r2-survey-2026-10-27.md)。

> 注（10-28）：層の名前・段・前提・規模・工数は [infinity-foundation-plan.md](infinity-foundation-plan.md) が正本。本書の値は調査時点の記録で、同書のレビューで再計測・修正されたものがある（例：R56・R49・R50・R37・R54・R65）。

## 1. 自動調査の要約（2026-10-27 12:4x、HEAD 時点）

想定する層の順序（暫定、調査で確定する）：
HomologicalAlgebra < DifferentialGraded < CommutativeAlgebra < Core < Universe/Categories/Coherent/KanModels/Transport/Cocartesian/StraighteningLeft
< F1 < F1B < HomotopyLimits < F2 < Stable < DGNerve/DoldKanComparison < Derived < KST/Spectra < LocalizingInvariants < SConstruction < Fibration
< NonConnective < Comparison < EInfinity < BhattScholze < CLMST < Paper < Inputs。

### 1.1 想定順序に対する逆向き import（上位 15、件数＝import 辺の本数）

| import 元 → 先 | 件数 | 例 |
| --- | ---: | --- |
| F2 → Stable | 193 | F2/Ind/YonedaCospanSquareFamily → Stable/Bicartesian |
| F1 → F1B | 90 | F1 集約 → F1B/Diagrams/ScaffoldUnderChain |
| Derived → KST/SConstruction | 84 | Derived/DGKappaPresentedSeedRefinement → SConstruction/DGModuleExtensionComposition |
| HomotopyLimits → F2 | 84 | HomotopyLimits/FiniteCommonFiberProductUniversal → F2/Presentable/SiftedFiniteFiberProduct |
| F1 → HomotopyLimits | 83 | F1/TwistedArrow/PointedDisplay → HomotopyLimits/UniverseLeftFibration |
| HomologicalAlgebra → CommutativeAlgebra | 63 | HomologicalAlgebra/ParameterKoszulIdempotent → CommutativeAlgebra/IdempotentImageBaseChange |
| F1B → Stable | 54 | F1B/KanExtension/ComparisonCartesian → Stable/CoconeRestrictionOppositeFibration |
| HomotopyLimits → Stable | 50 | HomotopyLimits/RelativeRightCosliceSection → Stable/CosliceRestriction |
| F1 → F2 | 28 | F1/KanModels/KanEquivalenceLiftingFibration → F2/CatInfinity/CoreIsofibration（第 1 窓からの持ち越し） |
| LocalizingInvariants → EInfinity | 26 | LocalizingInvariants/DGAlgebraSimplicialConvolutionRestriction → EInfinity/ComplexLimits/NormalizedMonomorphismCofibration |
| HomotopyLimits → KST/Spectra | 25 | HomotopyLimits/SpectrumTowerSequence → Spectra/CofibrantOmegaSequence（第 1 窓からの持ち越し） |
| Derived → LocalizingInvariants | 24 | Derived/DGKappaNativePComparison → LocalizingInvariants/ExactMapPinchedPath |
| Derived → NonConnective | 19 | Derived/DGSuspensionCoherentActionInput → NonConnective/DGSuspensionNativeActionInput |
| DifferentialGraded → KST/SConstruction | 13 | DifferentialGraded/Functor/ClosedConjugationPasting → SConstruction/DGFunctorHomConjugation |
| F2 → KST/Spectra | 12 | F2/FilteredExchange/PiCriterion/* → Spectra/UnbasedHomotopyIsomorphism（Ind-π） |

その他：Stable → Derived 10、F2 → Derived 7、F1 → Stable 23、HomologicalAlgebra → LocalizingInvariants 1（E2-S (8) の移動で生じた）、
CommutativeAlgebra → BhattScholze 5、Derived → EInfinity 5、KST 内の相互参照（LocalizingInvariants ↔ Fibration/SConstruction/NonConnective、Spectra → SConstruction/NonConnective/LocalizingInvariants）。
全 52 ペアの全件は付録。

R2-A の層順序提案（調査済み、実装前）：`Core < Foundation∞（F1・F1B・汎用 HomotopyLimits）< Stable.Base < F2 < Stable.F2Applications < Derived`。
HL と F2 の順序反転は採らず、Stable の汎用補題と F2 接続を分離する。指定9組は599辺、現在の計数も付録と一致。
各組の移動／分割／同一層としての文書化、R26/R27 の全参照先と工数は [R2-A 詳細](../r2-a-layers-2026-10-27.md) を参照。

### 1.2 どのモジュールからも import されないモジュール：850 本（うち監査スクリプトからの import 103）

DifferentialGraded 555（Checks 系が大半）、HomotopicalAlgebra 123、CategoryTheory 26、F2 20、CLMST 16、Derived 14、CommutativeAlgebra 13、BhattScholze 11、F1 9、他。
集約に未登録の葉・検査用モジュール・旧経路の残骸が混在する。分類（登録／削除／archive）が必要。

### 1.3 凍結候補（10-27 の設計変更で不要になったもの、41 本の機械抽出）

Derived/SuspensionAction の ε 経路（QuotientNative・NativeTarget・NativeEpsilon*・剛性）、Derived/CoherentBar/Compact の QuotientEpsilon*・
SuspensionFixedCoherenceTypes・Suspension*ConeComparison*、Derived/DGSuspensionCoherent*Input・NativeCoherenceProposal、
NonConnective の DGSuspensionCoherent*・EdgeIsoTransport。剛性定理と反例は診断として保持、主経路集約から外す。

### 1.3′ 監査被覆と集約（R2-D 完了 2026-10-27、[archive/r2-d-audits-aggregates-2026-10-27.md](../r2-d-audits-aggregates-2026-10-27.md)）

- 訂正：旧表の「未被覆 1,752 本」は scripts/audit_*.lean だけで数えた値。scripts/audit/*.lean（dg 2,144・shared 1,621 import ほか 5 本）を含めると
  監査 98 本の閉包は 33,449 本、未被覆 162 本（追跡済み 156、孤立 137、sorry 0、root 閉包との交わり 0）。KTheory・PerfectComplex・Paper の未被覆は消えた。
- 未被覆 156 の内訳：HomotopicalAlgebra/Simplicial 121（R2-B 未登録表の pure_compatibility_wrapper 123 行と一致、処置 delete）、F1/Diagrams 16、
  Derived/DGKappaPresentedSource* 11、DifferentialGraded/Functor 5、Spectra/SymmetricSequence 転送入口 3。
- 集約の統一基準（コメント除去後の本文で判定）：集約 135・転送入口 179・検査専用 278・互換入口 6。同名ディレクトリつき 34。KST は集約 23＋転送 1＋互換 2
  （K-B3 の 24／12 と一致。LocalizingInvariants・SConstruction の入口は import 以外の命令を含むため互換入口）。
- verify.sh の穴：実行する監査は 25／98。実行されない 73 本のうち公理・sorry 検査を持つもの 37（audit_axioms 本体 103 件、kst_comparison 1,500、kst_pro_excision 1,644、
  kst_s_construction_tail・kst_core_flag・BS/CLMST 系ほか）。scripts/audit/*.lean のみが import する 994 本（DifferentialGraded 957）は verify.sh でビルドされない。
- audit_targets.txt は verify.sh 実行時に再生成される派生物（現行との差分：追加 52・削除 130、削除は全て BS 側の Delta）。コミット対象から外すか、R 窓ごとに再生成する。

### 1.4 その他

- 300 行超の現行計画：foundations-progress（365）、perfectoidization-interface（1090）、k-theory-kst-route（480）、dg-theory-u12e-general-inventory（639）、
  L4（347）・L7（340）・L8（352）・L11（613）。
- 既記録の R 候補：NativePreservationPosetReductionUniverse と原版の統合、WeakString の q 版を closedStableFlagPost の特殊化へ、
  RawSpectrumRelativeCorner を NonConnective の相対 latching 正本へ、DGBarCompactSpacePiData を F2 へ、CellZeroObstruction を主経路外へ、
  F1/KanModels → F2/CatInfinity の 22 本、F1/HomotopyLimits → KST.Spectra の 4 経路、BS スタブ。
- 未追跡の作業ファイル（12:4x）：Spectra の PointedUncurry*・PointedParametric*（旧経路 WIP）、D・D-S・K-S•・HomotopicalAlgebra・DifferentialGraded/Morita の各 1〜3 本。

## 2. 事前調査の分担（読み取り専用、並列、各 1〜2 日）

| 調査 | 担当 | 範囲 | 成果物 |
| --- | --- | --- | --- |
| R2-A ∞ 圏基盤の層順序 | F2-St（設計評価の後） | Core・F1・F1B・HomotopyLimits・F2・Stable の相互参照（F2→Stable 193、HL→F2 84、F1→HL 83、F1B→Stable 54、HL→Stable 50、F1→F2 28、F1→F1B 90、Stable→Derived 10、F2→Derived 7） | 想定順序の確定案、各逆辺の処置（移動／分割／例外として文書化）、本数と工数 |
| R2-B Derived・DG・HomologicalAlgebra | D（4e3aa69df 完了）・D-S（b53587371 完了、[処置案](../r2-b-ds-2026-10-27.txt)・全 209 辺・未登録 678・凍結 41・近接複製表） | Derived→KST 127（指定 3 群：SConstruction 84・LocalizingInvariants 24・NonConnective 19；全体 133）、DG→SConstruction 13、Derived→EInfinity 5、HomologicalAlgebra→CommutativeAlgebra 63・→LocalizingInvariants 1、DifferentialGraded 未登録 555・HomotopicalAlgebra 123、凍結候補 41 | 分類表（登録／削除／archive／移動）、凍結の扱い、近接複製の対応表 |
| R2-C KST 内部 | K-B3（先行作業の後）・Sp-3（s3 後）・K-S•（③ 後） | LocalizingInvariants↔Fibration/SConstruction/NonConnective、Spectra→SConstruction/NonConnective/LocalizingInvariants、KST→EInfinity 29、KST→Comparison 45、WeakString・corner・KanPullbackAll・Thomason の重複 | 層順序案、近接複製の統合案、集約・監査の再編案 |
| R2-D 監査と集約 | コーディネータ（2026-10-27 完了） | 集約・転送入口・検査専用の分類、監査 98 本と verify.sh 実行 25 本の対応、未被覆 162 本、audit_targets 差分、ビルド漏れ 994 本 | §1.3′、[対応表](../r2-d-audits-aggregates-2026-10-27.md)、R41〜R43 |
| R2-E 計画検証 | R-V（2026-10-27 調査完了、コード変更なし） | foundations-progress・infinity-core-*・kst-lanes の37計画を照合。484コミット参照の実在、主要公開名・所有・依頼・R候補、決定15・16と10-27設計、300行超8計画の圧縮範囲を確認 | [不整合一覧・修正案・圧縮案](../r2-plan-verification-2026-10-27.md)。正本・各レーンへの修正反映は未実施 |

調査の規約：コードを変更しない。候補は本ファイル §3 に R26 から番号付けして追記する（一行一候補）。計画への記載だけでなくチャットでユーザーに報告する。

## 3. 候補一覧（R26〜、調査で追記）

- R26 F1→F2 の現28辺・26利用元・13参照先（旧22本の持ち越しを再集計）：core／関手同型を F1/F1B、一般錐判定を HL へ抽出。全プロジェクト259利用ファイル・294辺、16〜28h。公開名・型保持、下位の F2 推移依存と既存監査で検証（[詳細](../r2-a-layers-2026-10-27.md#r26f1f2-の28辺)）。
- R27 HL→KST.Spectra25辺＋F1→同2辺、計27辺・21参照先：Kan／π／tower の汎用17参照先を下位抽出、Spectrum*5本を KST/Spectra/Limits へ、PullbackFiberIso の過大 import を縮小。全プロジェクト156利用ファイル・175辺、24〜48h。下位の Sp 推移依存と既存監査で検証（[詳細](../r2-a-layers-2026-10-27.md)）。
- R28 NativePreservationPosetReduction と Universe 版：v = u の単純特殊化では統合不可（原版の任意 SSet.{u+1} と ulift C の差）。cofinal-poset の共通帰着核を共有し、公開 2 述語はラッパーで保持（D-S、1〜2 人日）。
- R29 WeakString の q 版を closedStableFlagPost_homotopyPullback の特殊化として導き直す。
- R30 RawSpectrumRelativeCorner{Step,Next,Family} を NonConnective の相対 latching 正本へ移すか、前合成版を二変数版の特殊化へ。
- R31 DGBarCompactSpacePiData は唯一の一般空間入力で複製ではなく配置問題。FilteredSpaceBridgeInput 全体を F2/FilteredExchange/PiCriterion へ移す。直接利用 7 本（F2 3・Derived 4）と 2 系統の監査を検証（D-S、0.5〜1 人日）。
- R32 CellZeroObstruction・NativeDiskPair・剛性定理を主経路集約から外し診断集約へ。各反例・剛性は異なる主張なので統合しない（D-S）。
- R33 凍結候補 41 の処置（D-S 分類）：診断 14・archive 19・維持／第 II 段再利用 8、証明の削除 0。再利用 8 のうち CoherentStage* 5 本は現行 cone 入力の bar 比較の依存鎖上にあり凍結不可（機械抽出の誤検出）、残る 3 本は cone 評価の単位／合成比較 2 と辺比較後合成 1。
- R34 E2-S (8) で生じた HomologicalAlgebra → KST/LocalizingInvariants（CochainConnectiveLift）の解消：truncation 持上げ 3 宣言を HA へ、単位・tensor の 2 宣言を DG 側へ分割（D-S）。
- R35 BS 側スタブ（旧入口の public import）の整理（BS セッションと調整）。
- R36 未登録モジュールの処置（D-S 分類、R42 と統合）：DG 555 のうち 552 は scripts/audit/dg.lean 登録済みの検査モジュール（主ライブラリ集約へは入れない）、固有未登録 3 本を登録；HA 123 は純粋互換入口 121 削除（正本と公開宣言は残す。15 入口を参照する check scripts を先に正本へ直し、外部互換期間の確認後に削除）・既隔離 Rectification.Foundations 1 維持・WIP 1 完了後登録。
- R37 Stable の汎用葉を Foundation∞ へ：F2/F1B/HL/F1→Stable の参照先和集合96本中86本を候補とし、残る10本・F2 から20辺は Stable.Base の順方向として維持。32〜64h、下位の Stable.Base 推移依存と公開型・全監査を検証。
- R38 HL→F2 の84辺・63参照先を汎用75辺／専門・混在9辺に分け、一般補題は下位、sifted/PΣ の適用は F2 へ。Stable→F2 の汎用40辺も共同処理、24〜48h、両方向の推移閉包と既存監査で検証。
- R39 Stable→Derived10辺・F2→Derived7辺：一般随伴／right fibration／slice を下位抽出、BridgeInput は R31、集約1辺は上位接続へ。Stable の真の F2 接続も分離。24〜48h、元の射・型・全監査を検証。
- R40 Core／Foundation∞／Stable.Base／F2／Stable.F2Applications の層規約と上位互換集約を分離。F1↔F1B・F1↔汎用HL は同一層内 DAG とし、R2-D と監査入口・個別例外を照合。8〜16h、直接辺・推移閉包・監査被覆を検証。
- R41 verify.sh のゲート強化：for 一覧を廃し scripts/audit_*.lean・scripts/audit/*.lean の全 98 本を実行、失敗 rc を集約して非零終了（K-B3 案）；ビルド対象に scripts/audit/*.lean の閉包（漏れ 994 本）を加える；audit_targets.txt は再生成のみでコミットしない。4〜8h、全監査の rc と所要時間を記録。
- R42 未被覆 156 本の処置：HomotopicalAlgebra/Simplicial 121 は R36（R2-B の delete 分類）へ統合；F1/Diagrams 16・Derived/DGKappaPresentedSource* 11・DG/Functor 5 は所有レーンが集約登録か archive かを決める；Spectra/SymmetricSequence 転送入口 3 は削除。4〜8h、監査被覆の再計算で検証。
- R43 転送入口 179・互換入口 6・検査専用 278 の台帳化：転送入口は R2-B の pure_compatibility_wrapper と同じ基準で削除／保持を決め、検査専用（Checks・Audit 系）は対応する監査スクリプトとの重複を点検。8〜16h、公開名の import 元ゼロを確認して削除。
- R44 SConstruction の一般 DG 基盤 28 対象と依存閉包 75 本を下位へ（Derived→SConstruction 40・DG→SConstruction 13 の 53 辺に対応）。残る混在部分は一般幾何と K アダプタに分割（D-S）。
- R45 LocalizingInvariants 24 辺・NonConnective 19 辺：安定圏・商・cone の一般部分を下位へ、K・BF の適用を上位に保持（D-S）。
- R46 Derived→EInfinity 5 辺：shuffle の共通座標・置換・符号補題を抽出（D-S）。
- R47 HomotopicalAlgebra→CommutativeAlgebra 63 辺：直接利用元 57 本の単純移動は不可。逆依存 291 本を影響範囲とし、R40 の層規約で基盤／環適用層を分ける（D-S）。

- R59 入口の修正（2026-10-28 全体調査 §5-1）：ルート `SerrePositivity.lean` が InfinityCategories の F2・HomotopyLimits・Coherent・DoldKanComparison を import せず、`F2.lean` は CatInfinity・FilteredExchange だけを import して残りは `#check` 1,497 行。Ind・Presentable・Compact・Idempotent が既定ビルドに入らない。`#check` 群を scripts/audit へ移し、F2 のサブ入口（Ind・Presentable・Compact・Idempotent）と HomotopyLimits をルートに登録。放棄した FilteredExchange の直接経路は入口から外す（R33 と同じ分類）。ルート閉包が増える分のビルド時間を計測。4〜8h（[全体調査](../repository-survey-2026-10-28.md)）。
- R60 孤立モジュールと休止領域の台帳（全体調査 §5-2・3、R36・R42・R43 と統合）：どこからも import されないもの（DG 555・HA 123・F1/Diagrams 102・FilteredExchange 72・散在 Checks* 143 ほか）と、休止・凍結・旧経路の領域（F2/FilteredExchange 2,129、F1/Cocartesian 618、HA/Rectification 415、Derived/ClosureFunctoriality 35、KST/Comparison・ProExcision 731、KST 第 II 段休止 4 ディレクトリ 1,283、Spectra 283）を一表にし、各行に「主経路／診断／archive／一般論抽出（外部調査の G 群）」を付ける。古い記述（DoldKanComparison 入口、foundations.md の γ4、k-theory-kst-route.md 冒頭、KST/Comparison 入口）の修正も含む。8〜16h。

- R61 ∞ 層とその外にある完全一致・ほぼ重複の解消（[外部調査 §3](../infinity-outside-survey-2026-10-28.md)・[全体調査 §7](../repository-survey-2026-10-28.md)）。
  - 本文が同一のもの：F1/Universe/PinchedHom ↔ F1B/Localization/UniversePinchedHom（本文 53 行が同一、名前空間だけ違う）。
  - SConstruction 側と ∞ 層側の対：CoreTrivialFibration・TrivialFibrationStability・RelativeInitialExtension・InitialBoundaryIso・PushoutTranspose・EdgeTargetColimit。
  - LocalizingInvariants 側と ∞ 層側の対：SuspensionExactFunctor・AdjunctionOfOpposite／OppositeAdjunction。
  - EInfinity 側：`localization_extension_exists`（F1B の `IsLocalization.exists_extension` と重複）。
  - 複数の場所にあるもの：Ex∞（EInfinity/Hammock と KST/Comparison）、MappingCylinder（3 か所）、CoherentTrianglePathMinimum（3 か所）、LastHornContraction（2 か所）。
  - 原本は ∞ 層の側に残し、参照を直接置き換える。8〜16h。
- R62 `fraction_ho_localization`（KST/LocalizingInvariants/VerdierFractionComparison.lean:44、private）を公開し、Stable/Verdier へ移す。
  ho(B/A) が Mathlib の `trW` 局所化であることを述べる補題で、三角圏の Verdier API（CategoryTheory）と ∞ 版を結ぶ。R48 と同時に行う。1h。
- R63 HA/ComplexLimits（3 本）が KST.LocalizingInvariants.CochainConnectiveLift を import している逆転を解消する。R34 と統合する。1〜2h。
- R64 Kan 複体と pointed 単体的集合の層を新設する（外部調査の Sp-S1・S2・S3・S5、SC-C3・C4・C5、KST/Comparison の Ex∞ と単体的ホモトピー、約 1,000 本）。
  - 置き場所は InfinityCategories/Kan・Pointed、または HA/Simplicial（R40 の層規約で決める）。
  - 先に SerrePositivity/Spectra/PointedSimplicialSet・Pointed の置き場所を決める。
  - HomotopyLimits → KST.Spectra（R27）と InfinityCategories → KST 175 辺の大半がこれで解消する。40〜80h。
- R65 Dwyer–Kan 局所化の層（EInfinity/SimplicialLocalization・Hammock・FrameHom の G 群、約 450 本）を F1B/Localization/DwyerKan と HomotopyLimits へ移す。
  - 前提として、BarrattEccles への import 1 本と Derived.CofinalLimitTransfer への依存 1 本を切る。
  - モデル圏の ∞ 局所化 `modelHammock_isLocalization` を一般論として公開する。24〜48h。
- R66 ∞ 中核を dg に依存しない形にする。
  - HomotopyLimits → DoldKanComparison.UniverseHomotopy → DGNerve.Join* → DifferentialGraded の経路を切る。F1 の 4 本と F1/Diagrams の DGNerve への import も切る。
  - これにより、Core・F1・F1B・HomotopyLimits・F2・Stable の閉包から DifferentialGraded がなくなる。監査を加えて固定する。16〜32h。
- R67 基盤の層だけが使っているのに論文の層に置かれているものを、基盤の層へ分類し直す：CategoryTheory/Monoidal（67 本）・NerveHomotopy・Quiver・Simplex・Enriched、GroupTheory/Coxeter、Inputs/Homotopy、CategoryTheory の Rectification 互換入口 25 本。4〜8h。

## 4. 実施順と検証

- 前提：Sp-2・Sp-3・K-S• が I-5・I-6 を閉じ、全レーンが「停止準備完了」を報告した後。
- 順序：R2-A の層順序確定 → 移動系（R26・R27・R34、F2→Stable 等の大口）→ 統合系（R28〜R31）→ 凍結・未登録（R32・R33・R36）→ 監査・集約の再編（R41〜R43）→ verify.sh（R41 後の全監査版）。
- 検証：`scripts/refactor/verify.sh`（全体ビルド・全監査・sorry 閉包）の全緑。数学的内容・公開名・型は保存。
