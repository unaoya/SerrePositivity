# D：coherent bar の compact 生成元（c2・c6・c7）

## 現在地と範囲
- ユーザーの追加割り当て。工程 A の無条件の変形 retract は完了し、専用集約・監査済み。
- 所有：Derived/CoherentBar/Compact/ の新規葉・All・専用監査。既存 CoherentBar/、D-e の KappaCovers/・KappaPerfect/、KST/・F2/ は読み取り専用。
- C1・B（87ecf98c0）・C2 と無条件 covers（0d474aaf8）は供給済み。c2 の評価空間保存は全 native κ-filtered coherent 図式について証明する。
- 現在の KappaCovers/StrictComparison は通常の strict 図式だけを扱う。これを κ-compact 性の全称条件へ代用しない。
- 01845eaeb：Compact.All 10291 jobs、専用監査21葉・223宣言、両主集約12630 jobs成功。両全体監査成功：Derived 25098宣言／2865モジュール、Stable 26163／3136、許容三公理のみ。d6edccd04：30葉の集約10300 jobs・監査313宣言成功、両主集約12639 jobs、両全体監査（Derived25188／2874、Stable26253／3145）も成功。
- 46a5b4978：両主集約12650 jobs、両全体監査成功（Derived25255宣言／2880モジュール、Stable26320／3151）。追加の宇宙・反転 π 自然性6葉は集約10322 jobs、専用監査435宣言／42葉を通過。
- チャットの24時間基準は2026-10-25 18:07 頃のまま。期限は10-26 18:07 頃。

## 三段目
1. [x] C1・B・C2・covers の公開型を照合。C2 は strict 図式の余極限頂点比較であり、評価空間保存とは別。
2. [x] representable の native Hom を Yoneda と評価へ接続。全シフトの比較を保持。
3. [ ] coherent 比較を通じた評価交換から、F2.Compact.IsKappaCompact による representable の κ-compact 性。
4. [/] 全シフトと κ 未満 sphere-free 基底の native κ-compact 性へ接続。
5. [/] DGKappaClosedCompactGeneratorCriterion を通じて七入力と dgKappaClosedProjectiveObjects_property へ接続（c6・c7）。
6. [/] 比較の実値が届いたら代入の系と DGKappaConeInput の実例を供給し、K-B へ公開名を報告。

## 既存入口
- DGModuleKappaCompactBasic・Shift・Binary・Cone・Coproduct・PerfectCriterion。
- DGKappaClosedCompactGeneratorCriterion の smallCoproduct・freeSphere・sphere-free・perfect・closedProjective 判定。
- Retract/DeformationRetract の無条件の修正包含と ModuleHomotopy。
- F2/Presentable の P-9 新規葉は読み取り専用 import 可。ordinary compact／perfect を native κ-compact の代わりにしない。

## 新規の比較入口
- Compact/RepresentableEvaluation：`dgBarCompactYoneda_forward`・`dgBarCompactYoneda_leftAction` は任意次数の後合成と評価の整合。`dgBarCompactRepresentablePinchedIso` は全 pinched 空間の評価同型。
- Compact/YonedaHomNaturality：`dgBarCompactYoneda_homNaturality` は全 Hom 複体の自然性、`dgBarCompactYoneda_strict` は同じ比較の厳密 dg 自然変換。
- Compact/YonedaNerveIso：`dgBarCompactYoneda_nerveIso` は独立の対象宇宙を共通宇宙に置いた全 nerve 関手同型。全 coherent 図式で前合成できる。
- Compact/NativeHomCriterion：`dgBarCompact_iff_nativeHom_preserves` は実半自由対象の native κ-compact 性と、実 Hom 空間関手の全 native κ-filtered 余極限保存の同値。
- Compact/ProjectiveHomCriterion：`dgBarCompactRepresentable_iff_hom_preserves` は同じ代表そのものの射影的頂点の全 Hom 保存による判定。分解を余極限計算の始域へ持ち込まない。
- Compact/GeneratorClosure：`dgBarCompactRepresentableShift_of_hom_preserves`・`dgBarCompactSphereFree_of_hom_preserves`・`dgBarCompactClosedProjective_of_hom_preserves` は全 native 図式での代表 Hom 保存を明示入力とする接続。c6・c7 の無条件供給とは扱わない。
- Compact/ConeInput：`dgBarCompactConeInput` は代表 Hom の全 native 保存と同じ代表系の covers を引数に K-7 の全フィールドを束ねる。coherent C1 の代入前の条件付き組立であり、実例の存在証明とは扱わない。
- Compact/EvaluationModuleNerveIso：`dgBarCompactProjectiveEvaluationModuleNerveIso` は射影的模型上の同じ代表 Hom と評価の全 R 加群値関手同型。
- Compact/NativeEvaluationSpace：`dgBarCompactProjectiveEvaluationSpaceIso` は全 native Hom 空間関手と実評価空間関手の全同型。`dgBarCompactRepresentable_iff_evaluation_preserves` が同じ代表の native κ-compact 性への必要十分条件。
- Compact/EvaluationGeneratorClosure：`dgBarCompactClosedProjective_of_evaluation` と `dgBarCompactConeInputOfEvaluationPreservation` が実評価空間の全 native 保存を消費する。covers は後者の明示引数。
- NativeAugmentationIdentity：`dgBarCompactNativeAugmentation_isIso` は bar 自身の native 余錐の閉増大の恒等性。
- HomologyCoconeCriterion：`dgBarCompactHomologyCocone_isColimit_of_cokernel` は元の全脚を保持する逆向きの余核判定。
- NativeHomologyColimit：`dgBarCompactNativeHomologyCocone_isColimit`・`dgBarCompactProjectiveHomologyCocone_isColimit` は同じ実 native bar 余錐の全整数次数の評価ホモロジー余極限性。
- 評価ホモロジーの余極限性と、評価空間の native 余極限性を区別する。後者と representable の compact 性は未完。

## 次の一手
- 設計変更は採用済み。Ind-π が一般の空間余錐判定を供給し、D は正確な Prop 入力の公開・評価 π とホモロジーの比較・各条件の導出・橋だけを引数に残した ConeInput を担当する。
- 宇宙分離版の poset 帰着は NativePreservationPosetReductionUniverse の F2.Ind.Compact.preservesKappaFilteredColimits_of_poset を使用する。
- Ind-π の公開目標は FilteredSpaceBridgeInput の DGBarCompactFilteredSpacePiBridge（Prop）。元の F・c と実 transition・脚を使う五条件を DGBarCompactFilteredSpacePiData で与える。π は n+1、境界が指定道をたどる球面円柱で基点を移送する。正次数の全射条件は全ての指定道に対する強い形（評価空間の単体的アーベル性を使う）。型と PiTransportMap の後合成を検証・葉監査済み。
- BridgePreservation は「橋＋同じ bar 余錐の π 条件」から全 native 評価保存への接続を対象ビルド済み。π 条件の導出は未完で、橋だけを残した ConeInput はまだ公開していない。
- ModulePiTransport・ModulePiHomology は単体的加群の全基点 π と Moore ホモロジーの自然な比較、任意指定道の移送を供給。HomologyChartsPiData は加群ホモロジー余錐の普遍性と自然な全基点チャートから五条件を導く。ModuleHomologyCharts は同じ実単体的加群余錐への特殊化。native 評価の実脚に関するチャート自然性は未完。
- PinchedModuleMap・StandardMooreNaturality・PinchedMooreNaturality は元の Hom 鎖写像と実 pinched Moore 比較の自然性。PinchedPiCohomology・EvaluationValueCohomology は全基点の正次数と π₀ を元の Hom／評価複体のコホモロジーへ同定（頂点比較であり脚自然性とは区別）。E2-S (8) の fcc305646 を PinchedCohomologyNaturality で代入し、切断自然性の引数は解消済み。
- LinearUnderlyingValueComparison の dgBarCompactLinearUnderlyingValueComparison_transportIso は、同じ線形係数の射と native 基礎空間関手の実辺作用の全空間比較を供給。EdgewisePiComparison は反転した線形空間の全基点 π の比較。EdgewisePiNaturality はこの比較の自然性、UliftPiNaturality・UliftPiZeroComparison は全基点 π・π₀ の宇宙比較の自然性。元の bar 余錐への代入を継続。
- Ind-π は実ホモトピー同値による指定道移送の反映も担当。D は同じ native bar の評価ホモロジー余極限性を、実評価空間のチャートへ接続する。
- 既存の代表生成元判定と新しい供給済み結論を区別し、明示入力だけの補助入口を実証拠と呼ばない。

## 運用
- 新規 sorry・公理・引用なし。深層編集・コピー・移動・改名・削除なし。
- K-S dg 一般論の追加 import は既許可58本に限る。追加が必要ならコーディネータ経由。
- 自分の All の終端後に専用監査。set -o pipefail、所有ファイルだけ git commit --only。
- 実施記録はコミットメッセージ。公開報告後は承認を待たず進む。
