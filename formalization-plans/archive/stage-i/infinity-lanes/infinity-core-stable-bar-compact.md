# D：cell graph 射影性・D-8 e 全入力懸垂作用

## 現在地と範囲
- D-8 の数学的供給は完了。本体は `2b085b584`。元の閉射影的代表系を使う。
- Compact.All 10433 jobs、75葉721宣言の専用監査、Derived・Stable の両集約12744 jobsは成功。両全体監査も成功：Derived 25594宣言／2919モジュール、Stable 26659宣言／3190モジュール（許容三公理のみ、両終端0）。
- 所有：Derived/（Gluing 以外）・DifferentialGraded・DGNerve・DoldKanComparison の新規葉・集約・監査。本計画は300行以内。KST は読み取り専用。
- C1・B（87ecf98c0）、C2・無条件 covers（0d474aaf8）、Ind-π の実橋（0ae97a051）を消費済み。
- 仮定：R : Type u、CommRing R、D : Type v、DGCategory R D、Small.{u} D、κ : Cardinal.{u}、Fact κ.IsRegular。cone・sphere-free・perfect の供給は ℵ₀ < κ。
- 新割当（2026-10-26）：先に K-S• の固定 graph 右制限の射影性、その後 D-8 e 全入力自然性。

## 三段目
1. [x] C1・B・C2・covers の公開型を照合。
2. [x] representable の native Hom を Yoneda と実評価へ接続。
3. [x] 全 native κ-filtered coherent 図式で実評価の余極限保存と representable の native κ-compact 性。
4. [x] 全整数シフトと κ 未満 sphere-free 基底の native κ-compact 性。
5. [x] 七入力の一般判定から dgKappaClosedProjectiveObjects_property の代表系へ接続（c6・c7）。
6. [x] 無条件 DGKappaConeInput・DGKappaPerfectInput と充満忠実性を供給。両全体監査と引き継ぎを完了。

## 公開入口
- `Compact/NativeEvaluationPreservation`：`dgBarCompactEvaluation_preserves`、`dgBarCompactRepresentable_isKappaCompact`。
- `Compact/UnconditionalConeInput`：`dgBarCompactRepresentableShift_isKappaCompact`、`dgBarCompactSphereFree_isKappaCompact`、`dgBarCompactClosedProjective_isKappaCompact`、`dgKappaConeInput_unconditional`。
- `Compact/UnconditionalPerfectInput`：`dgKappaPerfectInput_unconditional`、`dgKappaConeInput_unconditional_derivedFullyFaithful`。
- 以上の namespace は `SerrePositivity.InfinityCategories`。公開型は専用監査で #check 済み。cone 入力の公理依存は propext・Classical.choice・Quot.sound の三つ。

## 接続の構造
- `NativeHomologyColimit.dgBarCompactProjectiveHomologyCocone_isColimit` は元の native bar 余錐の全整数次数の評価ホモロジー余極限性。
- `LinearHomCohomology` は全基点の正次数・π₀ を元の Hom コホモロジーへ自然に比較。`PiChartTransport`・`PiChartEquivalence`・`UliftPiChart` は指定道と実全空間比較を保持する。
- `ModuleValuePiChart`・`ModuleValueNaturality` は dg Yoneda により元の評価複体へ戻す。`EvaluationEdgeNaturality` は任意の元の native 辺での自然性。
- `CoconeLegNaturality`・`EvaluationCoconeGeometry` は後合成・添字制限・宇宙持ち上げと元の実脚を照合する。任意の同じ余錐について証明し、最後に実 bar を代入する。
- `EvaluationHomologyCoefficients`・`EvaluationHomologyCharts`・`EvaluationChartNaturality`・`EvaluationChartLegs` は同じ H⁰ 図式の対象同型・transition・脚を合わせる。
- `NativeEvaluationPiData` はホモロジー余極限から五条件を無条件に導出。Ind-π の `FilteredSpaceBridge.dgBarCompactFilteredSpacePiBridge` を代入し、`NativePreservationPosetReductionUniverse` の宇宙分離版で全 native 図式へ戻す。
- `EvaluationGeneratorClosure` の七入力への一般接続へ実評価保存を代入し、D-e の `dgKappaCone_covers_unconditional` と同じ代表系で組み立てる。`KappaPerfect/Input` の実比較も同じ cone 入力へ代入する。

## 引き継ぎ
- κ-compact 性は `F2.Compact.IsKappaCompact.{u, max (u+1) v}`。ordinary compact／perfect による代用や native 図式の strict 化は行っていない。
- κ と添字は宇宙 u、対象は独立の v。橋・保存性・比較・covers は最終入力の追加仮定に残さない。
- 現模型の変更はない。DGSuspensionNativeActionInput は第 I 段中の明示入力を維持。
- D-9 は D 側残件なしとして完了記録済み（8924d1cee）。
- 旧 D-8 は `2b085b584` で完成、`a92d893c7` で close。今回の D-8 e は別の未完了作業。

## 運用
- 新規 sorry・公理・引用なし。深層編集・コピー・モジュールの移動・改名・削除なし。
- K-S 一般論の逆 import は追加しない。新しい型用の読み取り専用 import は DGCellResolvedGraphPerfect・DGGluingCellRightAxisPerfectArrow の二葉。F2 の供給葉は読み取り専用。
- 根の lake build SerrePositivity と .lake の削除はしない。両主集約の終端を確認してから全体監査。
- set -o pipefail、所有ファイルだけ git commit --only。実施記録はコミットメッセージ。

## 新割当 (1)：K-S• 射影性
- [x] 固定 `dgCellResolvedGraphResolution` の各右制限の射影性。任意 B・任意自己関手 F に一般化して証明。
- [x] `DGCellSourceProjective.dgCellSourceHom_isKProjective`：同じ cell source の全 Hom は K-projective。
- [x] `Derived/RestrictionProjective`：制限後の生成 sphere の射影性から、全次数分裂と全射 Hom tower で semifree 制限の射影性。
- [x] `Derived/BimoduleRightProjective`：相手側の全 Hom の K-projective 性を、同じ標準 bimodule 解像度の各右制限へ適用。
- [x] 公開 `InfinityCategories.dgCellResolvedGraph_projective R B F : KST.SConstruction.DGCellResolvedGraphProjectiveCondition R B F`。
- [x] 公開 `InfinityCategories.dgGluingCellRightAxisProjectiveInput R C D M z hz`：右軸と恒等の二証拠。DGOdotGluing を含む全 gluing に適用。
- [x] Derived 集約 12508 jobs 成功。専用 `scripts/audit_derived_cell_projective.lean`：11葉48宣言、許容三公理のみ。局所 import 閉包1338モジュール、循環なし。
- [x] 追加後の Derived 全体監査：25642宣言／2930モジュール、許容三公理のみ、終端0。所有ファイルだけコミット。
- 旧未追跡3葉は既存 `DGFunctorThickHomCriterion` と用途が重複し、SConstruction 一般論の逆 import を含む。採用せず削除。退避 `/tmp/d-new-chat-residuals/`。

## 新割当 (2)：D-8 e（未供給）
- 正本：`archive/stage-i/kst-lanes/L10-nonconnective.md` 100–110・144–148行。
- 同じ実核・cone・零角・懸垂の全族 `((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity R) ⟶ dgKInputInfinity R`。
- 各 A への制限は `dgKappaResolvedConnectiveSquare R A (s A).cone` の四角形全体と厳密一致。
- 同じ実評価 Morita 比較、元の P の包含について全 native Hom 自然性を供給する。
- 供給路は PerfDGInput の厳密 SSet 豊穣自己関手の coherentNerveMap。閉射影的代表系・cone・I・P・固定 S・ν・K は変更しない。
- [ ] 全 native Hom 上の cone・実核・零角・懸垂作用と厳密単位合成。
- [ ] 元の選択された四角形全体を保持する全族。
- [ ] 実評価 Morita 比較と元の P の包含の全 native Hom 自然性。
- [ ] 全仕様の公開型が確定した時点で K-B3 向けに報告。完成まで報告を待たない。
- 全四角形・懸垂成分の中間型 `DGSuspensionNativeSquareModel R s` を先行公開・報告。11297 jobs で成功、局所 import 閉包7493モジュールに循環なし。存在と Morita・P 自然性は含まず、全仕様の完成型ではない。専用 `audit_derived_suspension_native.lean` は23宣言、許容三公理のみ。
- 注意：元の四角形は指定収縮と零化四角形の存在定理から選んだ全二胞体を含む。四辺・四頂点の一致だけでは全族の厳密一致にならない。
- 既存の対象別 covers・通常 dg 射の条件付き恒等合成・P 選択不変性を全入力自然性の供給済みとは数えない。

### D-8 e 本体：固定分解への作用（作業中）
- 初期 cycle 被覆・固定対象増大の比較・境界 cell 付加・全段階・実余極限の順に、元の比較の恒等／合成を厳密に証明。
- `DifferentialGraded.DGCategoryCellResolution.comparisonFunctor_identity`・`comparisonFunctor_composition` を公開。元の `comparisonFunctor` 自体の等号で、増大後／導来圏での等号に弱めていない。
- `InfinityCategories.dgKappaSuspensionMapDataOfCone_identity`・`dgKappaSuspensionMapDataOfCone_composition` は、既存 `ofConeFunctor` の同じ分解データの厳密則。
- `InfinityCategories.dgKappaSuspensionInputMapOfCone_identity`・`dgKappaSuspensionInputMapOfCone_composition` は同じ実平坦商の入力射の厳密則。
- 以上の各段の公開名はユーザーへのチャットでも報告済み。通常射の則だけでは全 native Hom の作用・全四角形族を供給済みと数えない。
- Derived 集約14639 jobs成功。新規6葉の専用 `scripts/audit_dg_cell_comparison.lean`：49宣言、許容三公理のみ。追加後の全体監査25688宣言／2936モジュール成功、許容三公理のみ、終端0。局所 import 閉包7301モジュール、循環なし。
- 次の中心課題：同じ選択代表系へ全 native 入力の作用を構成する。元の加群延長の値が選んだ代表と導来同型であることと、同じ代表系への厳密豊穣作用の存在を混同しない。
- `DGKappaPresentedSourceObject`／`DGKappaPresentedFreeObject` の旧試作で模型を置き換えない。固定 cone・I・P の上で作用を作り、選択された四角形全体への一致まで証明する。

### D-8 e 本体：同じ実商の全パラメータ自然性（作業中）
- `DifferentialGraded.DGQuotient.parameterExtension`：任意の複体 K をパラメータとする元の変換を、選択された収縮との整合から同じ実商へ延長。全整数次数・元の全成分を保持。
- `parameterExtension_exists_iff`：同じ全成分を保持する延長の存在は、全 k・全 K の元での指定 ε 自然性と同値。元 Hom だけでなく全有限 path について証明した。
- `parameterExtension_unique`・`parameterExtension_reindex`：同じ全成分による一意性と、任意のパラメータ射による制限との厳密可換性。
- 公開名はユーザーへのチャットでも報告済み。これは商作用の構成部品であり、実選択された C(A) の ε 整合性や全族の存在を供給済みとは数えない。
- Derived 集約14643 jobs成功。新規4葉の専用 `scripts/audit_dg_quotient_parameter.lean` は59宣言、許容三公理のみ、終端0。4葉追加後の全体監査25747宣言／2940モジュール成功、許容三公理のみ、終端0。
- 次：同じ選択代表系の cone・実核作用を全 native Hom 上で構成し、元の選択収縮に対してこの ε 整合条件を実証する。条件を最終入力として追加しない。

- `DGQuotient.parameterExtension_postcomposition`：同じ選択収縮の後合成族は、任意パラメータ・全次数の元の自然性から ε 整合を実証して商へ延長。
- `parameterExtension_postcomposition_heq`：元の厳密 `extension_postcomp` 等号の下で、全パラメータ変換も元の前合成作用そのものと比較。公開名はチャットで報告済み。
- この後合成の経路では ε 整合を追加入力に残さない。全入力を動かす cone・実核作用と同じ選択四角形の全族はまだ未供給。
- 後合成を含む5葉版の Derived 集約14644 jobs成功。専用監査は5葉76宣言、許容三公理のみ、終端0。追加後の全体監査25764宣言／2941モジュール成功、許容三公理のみ、終端0（/tmp/d8e-post-full-audit.log）。

### 元の選択四角形全体への復帰
- `nativeDiagramFamily_relativeReplacement`：予備の全図式族と、指定部分を固定する各入力の全可逆 path から、同じ部分制限を保つ全比較族を実構成。指定 path 自体も厳密に回収。
- `dgSuspensionNativeSquare_exists_replacement`：同じ元の `dgKappaResolvedConnectiveSquare` 全体へ各入力で厳密一致する全族を構成。指定単射部分の全 native 作用を厳密に保持。四辺だけの一致で全二胞体を同定しない。
- 公開名と設計はユーザーへのチャットで報告済み。予備族と指定部分に相対的な点別可逆 path の存在は未供給。実核・cone・懸垂の厳密豊穣作用や Morita・P 自然性を完成扱いしない。
- 設計：先に構成した全族を、零骨格上の指定全比較を保つ相対 path の自明 Kan 持ち上げで元の選択へ戻す。P の指定包含にも同じ方式を検討する。単なる対象同型ではなく、指定部分上で恒等 path になる全比較が必要。
- 二葉の対象 build 11297 jobs・Derived 集約14833 jobs成功。専用監査は2葉3宣言、許容三公理のみ、終端0。局所 import 閉包7493モジュール、循環なし。追加後の全体監査25766宣言／2943モジュール成功、許容三公理のみ、終端0（/tmp/d8e-replacement-full-audit.log）。

### 同じ P/Yoneda 比較の全入力延長
- `dgKappaNativePExactMap` は元の P・元の Yoneda・元のラベル評価を保持する完全関手。`dgKappaNativePComparisonPath` は既存の指定 Morita 逆比較の実辺を使い、境界で全 path が厳密に定値となる。
- `dgKappaNativePFamily_exists`：同じ実評価 Morita 比較の全族 M を先行入力にすると、元の P/Yoneda 包含と指定比較の全族を実構成。全 ν 両端を固定し、各入力の同じ全比較 path を厳密に回収する。比較の全入力自然性を別の入力として残さない。
- 公開型 `DGSuspensionNativeNaturalityModel R s` は同じ全四角形・豊穣懸垂成分と Morita 全族を保持する。`moritaIso` は全 native 入力に自然な同型を導出。`perfectFamily`・`perfectComparison`・`perfectComparison_at`・`perfectFamily_boundary` もそのデータから導出される。
- 公開名と未供給範囲はチャットで報告済み。この型の存在、先行する四角形族と Morita 全族、元の導来模型での P.inclusion 自体の全入力比較は未供給。D-8 e 全仕様の存在証明や完成型と混同しない。
- 対象 build 11764 jobs・Derived 集約14897 jobs成功。専用監査は3葉62宣言、許容三公理のみ、終端0。局所 import 閉包7958モジュール、循環なし。追加後の全体監査25849宣言／2947モジュール成功、許容三公理のみ、終端0（/tmp/d8e-native-p-full-audit.log）。
- 固定閉代表族への厳密豊穣持上げの既存供給は他レーンにないとユーザー経由で確認。新しい仮定は採用していない。厳密供給路が入力の厳密同型を同じ懸垂の対象型の全単射まで保つ必要性を Lean の試作で確認（/tmp/D8eStrictIsoProbe.lean）。これは現模型での不存在の証明ではない。

### 固定懸垂の緩和境界（B1 採用、B2 不採用）
- 判断 (a)：上記相対 path の持ち上げは SSet 射と全比較を供給するが、固定対象上の厳密豊穣単位・合成則を生成しない。この経路での厳密則完成の見積りは出さない。不存在の主張ではない。
- 案 B1 `DGSuspensionCoherentActionInput`：採用条件どおり map・厳密 vertex・実 data を保持し、edge 等号を端点固定 `intervalMappingSpace` 内の `VertexIso` に変更。`ofStrict` で現行入力から埋込み。
- `DGSuspensionCoherentSquareInput` は同じ全四角形の厳密一致を保ち、上位型の enriched・enriched_obj・enriched_map 要求を除く。edge だけの変更では厳密豊穣則の問題は残る。反復辺の等号を使う消費側は比較輸送へ変更が必要。
- B2 はユーザー判断で不採用。旧提案葉と専用監査を採用 B1 の二葉・専用監査へ置換し、B2 API を正本へ登録しない。
- 実体供給の順：相対同値 path による全 map → edgeIso → 同じ全 square_at → 実評価 Morita／元の P 包含の全 native 自然性。先行全族と指定相対 path の存在はなお未供給で、延長定理だけで無条件存在を主張しない。
- ユーザー指示で採用名を Derived 集約・全体監査へ登録。map・vertex・data、全 square_at、suspension 角等号は保持し、edge だけを端点固定 VertexIso に緩和。action／square の ofStrict を保持。KST は読み取り専用。
- 旧提案段階の検証：対象 build 11299 jobs・専用監査66宣言成功。これは B1／B2 の無条件存在の証明ではない。
- 再開時見積り：型の公開・検証・コミットは初回ターン、実体供給は暫定1〜2日。先行全族・指定比較の構成可能性を確認して更新する。公開名・見積りはユーザーへのチャットでも報告。
- 採用二葉の対象 build 11300 jobs成功。専用監査43宣言／2モジュール、許容三公理のみ、終端0。Derived 集約14900 jobs成功。局所 import 閉包11173モジュール、循環なし。追加後の全体監査25892宣言／2949モジュール成功、許容三公理のみ、終端0（/tmp/d8e-adopted-full-audit.log）。採用 API は51b5cc8daで公開。

### 実 Morita／P/Yoneda 全族の無条件構成（固定源の核作用との一致は未供給）
- `dgKappaNativeMoritaFamily`：実評価 Morita 辺の点別可逆性と path 始点評価の自明 Kan 性から全入力族を構成。`source` は固定 ν の全作用そのもの、`at` は同じ実 Morita 辺全体の厳密回収。
- `dgKappaNativeKernelStableFamily` と `dgKappaNativeMoritaFamily_iso` は、その終点 StableInfinity 値と全 native 入力に自然な同型。終点を固定 S 内の核作用の ν 像と同定したわけではない。
- `dgKappaNativePComparisonFamily`・`dgKappaNativePArrowFamily`：実構成した Morita 全族を既存21:25の相対延長へ代入。Morita 全族を追加入力に残さず、元の全 P/Yoneda 比較 path を at で厳密回収、boundary で全入力の両端作用を厳密固定。`iso` は全入力の指定同型。
- 初期 S 内全族、懸垂の map・edgeIso・square_at、核角の ν 像との全単体一致、元の導来模型での P.inclusion 全族は未供給。B2 や模型変更は採用しない。これらの新族だけで D-8 e 完成と数えない。
- 検証：対象 build 11764 jobs・Derived 集約14903 jobs成功。新規二葉の専用監査27宣言、許容三公理のみ、終端0。追加後の全体監査25919宣言／2951モジュール成功、許容三公理のみ、終端0（/tmp/d8e-native-family-full-audit.log）。実構成は9131e7b37で公開。

### B′ 新割当：D-1 → D-2 → D-4b（D-S の D-4a と接続）
- 所有は新しい sphere-only 基底関連葉、CoherentBar/Compact・KappaPerfect とこの計画。既存基底族・旧 cone/P の入口は編集しない。ClosureFunctoriality・SuspensionAction は D-S 所有。
- D-1 `dgKappaSphereClosureObjects_smallSemifreeRetractCovers`：各層 κ-small な実 semifree 加群の K(D) retract を、新しい sphere-only 閉包の実加群でホモトピー同型まで被覆。可算直和・全閉射の cone と指定 telescope 分裂を使用。対象 build 8897 jobs成功。
- D-2 `dgKappaConeInput_unconditional' R D κ hκ`、`dgKappaPerfectInput_unconditional' R D κ hκ`：新族の全 covers・perfectCovers・全写像空間比較同値を追加仮定なしで供給。対象 build 10441 jobs成功。末尾は ASCII prime。公開型はチャットでユーザーへ先行報告。
- 新 `objects` は `dgKappaSphereClosureObjects R D κ` に定義上等しい。基底は `dgKappaSphereClosureBaseFamily` の sphere-free だけ。perfect 小模型の基底を再追加せず、finite cell の retract を telescope で代表化して perfectCovers を再導出。
- covers は旧 covers の実被覆を、新族による旧族のホモトピー被覆へ合成して移送。新族の定義は旧族に依存せず、旧族の定義・定理は不変。新族の旧族への所属で既存の κ-compact 証明を再利用する。
- D-4b：D-S の新模型 map・edgeIso を待ち、同じ全 square_at と核角の ν 像への厳密接続を構成する。9131e7b37 の二族は任意の段提供者に適用でき、新段にも追加 Morita/P 入力なしで特殊化可能。全四角形の存在・ν 像との全単体一致は未供給。
- 検証：新11葉の専用監査51宣言、許容三公理のみ、終端0。Derived 集約14914 jobs成功。全体監査25970宣言／2962モジュール成功、許容三公理のみ、終端0（/tmp/d8e-sphere-full-audit.log）。4cd747153でコミット済み。旧基底族は無変更。

### D-4b 新模型の核射と比較族（全四角形は未供給）
- 新段提供者は K-B3 の `354e05773`、実射 data は D-S の `8fa7ccdef` を使用。KST と D-S 所有葉は読み取り専用。
- `dgKappaSphereClosureNativeMoritaFamily`・`dgKappaSphereClosureNativeMoritaIso` と `dgKappaSphereClosureNativePComparisonFamily`：9131e7b37 の全 native 比較族を新段へ特殊化。at の型に新 I/P を明記し、元の実評価辺と全 P 比較 path を厳密回収。対象 build12985 jobs、専用監査36宣言／3モジュール成功。
- `dgKappaSuspensionMap_preservesKernel`：実 resolved 射の零化対象保存を、零・同型・全 cofiber/fiber の帰納で実安定核全体へ延長。`dgKappaSuspensionKernelFunctor` は元の resolved の全 Hom をそのまま制限する。
- 新模型の `dgKappaSphereClosureKernelInputMap`・`dgKappaSphereClosureNullInputMap` を供給。`KernelInputMap_inclusion`・`SuspensionInputMap_projection`・`NullInputMap_left` は同じ実 dg 入力で三面の厳密可換性を証明。対象 build12792 jobs成功。
- 残りは全 native 入力の四角形族・選択された全二胞体への square_at・核角の ν 像と上記 Morita 終点作用の全単体一致。通常射の三面だけで完成としない。D-S への段提供者名の中継後、D-4a の再開を確認。
- 新二葉を Derived 集約・全体監査・専用監査へ登録。Derived 集約14929 jobs、専用監査47宣言／4モジュール成功。許容三公理のみ。局所 import 閉包9188モジュール、循環なし、外部未コミット依存なし。全体監査25990宣言／2964モジュール成功、許容三公理のみ、終端0（/tmp/d4b-full-audit.log）。

### D-4b 実安定核への全次数制限
- `dgFullRestrictionFunctor`：対象条件を保つ dg 関手の充満 dg 部分圏から、同じ二部分圏の dg 関手圏への厳密 dg 関手。元の全 Hom end を制限し、評価で単位・縦合成を証明。
- `dgFullRestrictionNativeMap`：その標準 coherent nerve の core 上の全単体写像。`inclusion` で元の全単体作用を厳密回収。D-S 所有葉への依存はなく、公開名をユーザー経由で先行報告。
- `dgKappaSuspensionKernelParameter`・`dgKappaSuspensionKernelHom` は同じ実 data の resolved 変換を実核へ制限。app／π は同じ対象の元の成分、identity／composition は同じ tensor パラメータの厳密則。
- 入力 A,B を動かす resolved 全 Hom 作用や全四角形自体の存在は、この制限部品だけでは供給済みとしない。残る指定収縮・全二胞体比較と D-S の map／edgeIso の接続は継続中。
- 検証：新二葉を Derived 集約・全体監査・専用監査へ登録。Derived 集約14931 jobs、専用監査70宣言／6モジュール成功、許容三公理のみ。局所 import 閉包8972モジュール、循環なし、外部未コミット依存なし。追加後の全体監査26014宣言／2966モジュール成功、許容三公理のみ、終端0（/tmp/d4b-kernel-native-full-audit.log）。445404f65でコミット済み。
- 指定収縮は各対象の零性から選ばれている。対象ごとの零性・収縮比較から、厳密自然変換 end 内の同型や全四角形の相対 path を自動的に推論しない。指定 ε の全次数整合は実際に証明する。
- 依存待ち：D-S 稼働中で、map・edgeIso は未供給であることを連続3ターン、実ソースと thread 状態で確認。D は外部供給待ちで blocked。D-4a の採用 action 公開後、同じ指定収縮と全四角形への比較、square_at、核角 ν 像との全単体一致を再開する。D-4b 完了とは扱わない。

### D-S 工程2：固定 ε 整合 Hom の商関手変数
- ユーザー割当で固定 ε の商関手圏への豊穣延長を担当。D-S 所有葉は読み取り専用。D-4b 後半は従来どおり D-S の map 待ち。
- 依頼された一般形（null 保存関手の充満 dg 圏を源、対象は元の quotientDGFunctor）は、厳密自然同型の保存に障害。ℚ 上の一対象 C と二つの同型対象の D、S/T 全対象の例で、商関手間の次数0自然性は独立語 ε₀u と uε₁ の係数を等置し、成分が零に限られる。入力の非零自然同型と逆の合成保存に矛盾。数学的反例であり、反例全体の Lean 形式化は未了。
- 元の変換成分を保持しないという自由も上の例では解決しない。元の型の実装を進めず、ε 整合 Hom への源の変更か反例形式化の優先かをユーザーへ照会。
- `DGQuotient.parameterExtension_identity_epsilon`・`parameterExtension_composition_epsilon` は ε 整合の単位・tensor 縦合成での閉性、`parameterExtension_identity`・`parameterExtension_composition` は同じ成分の延長の厳密則。新規葉 QuotientParameterLaws、対象 build1958 jobs成功。一般形の存在主張は含まない。
- ユーザー判断：反例定理は作らず数学的記録のみ。工程2を ε 整合 Hom の部分複体を持つ NullPreservingFunctorsε 版へ変更して続行。対象作用は同じ quotientDGFunctor に固定し、D-S が resolvedInputFunctor の着地を証明する。先行則の検証：Derived 集約14933 jobs、専用監査82宣言／6モジュール、許容三公理のみ、終端0。
- ε 整合版の三葉 QuotientEpsilonHom／Category／Criterion が対象 build2591 jobs成功。`InfinityCategories.NullPreservingFunctorsε` は元の null 保存関手を対象とし、Hom は元の Hom end へ mono で入る pullback 部分複体。
- `quotientEpsilonCompatible`・`quotientEpsilonHomLift`・`quotientEpsilonHom_factor_iff`：任意複体パラメータで、部分複体への着地と各 b・全整数次数の元の固定 ε 整合が同値。追加の延長選択は入力に残らない。
- `quotientInputFunctor` と `quotientInputFunctor_obj` を公開。対象は元の同じ quotientDGFunctor へ厳密一致。縦の全 Hom の単位・合成保存も証明済み。ユーザーへのチャットで型と着地 API を先行報告。横の単位・合成の全単体整合は継続中。
- ε 整合版三葉を集約・専用監査・全体監査へ登録。Derived 集約14936 jobs、専用監査171宣言／9モジュール成功、許容三公理のみ、終端0。局所 import 閉包402モジュール、循環なし、外部未コミット依存なし。横の全単体整合は次工程。

- `nullPreservingFunctorsεLiftOfComponents`：元の豊穣作用と商上の全 Hom 作用の同じ成分比較から着地を束ねる。縦の則は元 Hom への mono 包含で反映し、商上の単位・合成則を追加入力に残さない。
- `DGQuotient.quotientDGFunctor_id`／`quotientDGFunctor_comp` と `quotientDGFunctor_original`：正本商の厳密な対象関手の単位・合成、および元 Hom 回収。対象 build1951 jobs成功。
- `quotientEpsilonNativeMap`／`quotientEpsilonNativeMap_unit`：同じ実 dg 商作用から作る全 native core 写像と、全単体の横の単位保存。対象 build5025 jobs成功。横合成は全 Hom 成分比較を構成中。
- 上記三葉を Derived 集約・専用監査・全体監査へ登録。Derived 集約14939 jobs、専用監査194宣言／12モジュール成功、許容三公理のみ、終端0。横合成はまだ完了としない。
- 最新指示：D-S 工程1は dg 関手圏間の dg 関手では成立せず、native Kan core 間の全単体 SSet 射へ変更。D の消費境界も SSet とし、D-S の coherentNerveMap／native core の型指定到着後に接続型を確定する。既存 ε 整合 dg 圏と native 商作用は下位 API として保持し、D-S がその dg 圏へ着地するとは仮定しない。
- D-S 計画の工程2消費型（native core）を確認。`quotientEpsilonNativeMap` は要求された core(dgNerve NullPreservingFunctorsε) → dgFunctorNativeMappingSpace QC QD と厳密に同じ型・同じ定義。ε Hom／quotientInputFunctor の型は変更不要。`quotientEpsilonNativeForget` と Map_vertex／Forget_vertex を追加し、元の関手・固定 ε 商関手の同じ頂点を厳密回収。
- `quotientEpsilonHorizontalFunctor`／`quotientEpsilonHorizontalFunctor_quotient`：同じ null 保存関手の横合成を全 Hom で ε 整合圏へ持ち上げ、正本商作用と dg 関手全体で交換。対象の等号移送は Hom end の抽象的相殺補題で処理。
- `quotientEpsilonNativeComposition`／`quotientEpsilonNativeMap_composition`：元の native tensor 比較から作る横合成について、全単体の SSet 射として comp_STU ≫ Q_SU = (Q_ST ⊗ Q_TU) ≫ comp_quotient を証明。対象 build5030 jobs成功。D-S の ε core への全単体着地、および D-4b の map／square 後半は供給済みと扱わない。
- 最終検証：Derived 集約14943 jobs、専用監査222宣言／15モジュール、全体監査26161宣言／2976モジュール成功。許容三公理のみ、すべて終端0。新葉の局所 import 閉包1356モジュール、循環なし、外部未コミット依存なし。D-4b 後半はユーザー確認どおり D-S の map 待ちを維持。

### D-S 工程4：固定端点 edgeIso の準備
- ユーザー割当で Compact の新規三葉 NativeMappingVertexEdge／SphereClosureQuotientEdge／SphereClosureEdgeIsoAdapter を追加。D-S の NativeTarget は読み取り専用。
- `dgNativeMappingVertexEdge`：native Hom の零単体を、元の通常射との実同値を使って同じ二入力の標準辺へ読む。Hom 内の一単体と入力 nerve の一単体を区別する。
- `dgSuspensionQuotientNativeEdge` は dgSuspensionQuotientNativeMap を f の正本 resolved ε 頂点で評価した零単体から読む辺。`dgSuspensionQuotientNativeEdge_eq` は切替後の同じ cone・正本 data の coherentNerveEdge と厳密一致する。
- `dgSuspensionQuotientNativeEdgeIso` はその厳密一致から作る、固定端点 intervalMappingSpace 内の指定 VertexIso。両端の dg 入力は動かさない。型をユーザー経由で D-S へ先行報告済み。
- `dgSuspensionEdgeIsoOfQuotientComparison`／`dgSuspensionEdgeIsoOfQuotientEdgeEq` は、最終 dgSuspensionMappedEdge から商作用辺への指定同型／一単体等号を受け取り、採用 edgeIso と同じ型を返す。最終 map やその辺比較の存在は未供給。D-4b 後半 square／square_at は map 待ちを維持。
- 対象・集約 build14949 jobs、専用監査81宣言／9モジュール成功、許容三公理のみ。import 閉包9163モジュール、循環なし。D-S NativeTarget の追加もコミット済みとなった。今回消費する core／object／vertex／map／map_vertex の五宣言は HEAD と本文一致を確認。
- 最終全体監査26170宣言／2979モジュール成功、許容三公理のみ、終端0。専用監査も終端0。コミット前の import 閉包再確認で循環・外部未コミット依存なし。準備比較は完成し、最終 map の辺比較と D-4b 後半は D-S の供給待ちを維持する。

### 固定 data の恒等・合成の比較
- 追加依頼：固定 data の恒等入力と実懸垂の恒等射、および固定合成入力と二つの実入力射の合成を、同じ端点固定 intervalMappingSpace 内で比較する。ε 圏の単位・合成則では代用しない。
- `DGSuspensionFixedUnitComparison`／`DGSuspensionFixedCompositionComparison` の型を先行公開。右辺はそれぞれ実懸垂の恒等射／固定入力射二本の合成。入力射自体の厳密等号からの OfEq アダプタも提供。無条件の比較実体はまだ供給しない。
- D-S へユーザー経由で型を報告済み。cone の全 Hom 自然な実比較と、固定 cell 分解・商の関手圏での比較を区別して構成を進める。
- 型の先行検証：SuspensionFixedCoherenceTypes build12988 jobs、Derived 集約14950 jobs、専用監査87宣言／10モジュール成功。許容三公理のみ。固定比較の無条件存在とは扱わない。
- `dgSuspensionFixedUnitInputEqOfConeEq`／`dgSuspensionFixedCompositionInputEqOfConeEq` は、固定 cone 作用の厳密等号を明示入力として、正本 resolved・商の入力射の厳密等号へ移す。固定代表選択がこれらの仮定を満たすとは主張しない。
- `dgSuspensionConeRepresentativeIso` は固定代表化と実加群延長の、同じ実 dg 関手 end 内の全 Hom 自然な閉同型。共役の比較を対象評価だけの自然同型へ落とさず構成した。
- `dgSuspensionUnitConeEvaluationIso` と `dgSuspensionCompositionConeEvaluationIso` は、固定恒等 data／固定合成 data を、それぞれ恒等作用／固定 data 二本の合成と実加群評価後に全 Hom 自然に比較する。加群延長の単位・合成比較と dg 前後合成を用い、対象・Hom・代表選択を変更しない。
- 残る供給境界：これらの全 Hom 比較を固定 cell 分解・固定 ε 商へ持ち上げ、上記の固定端点 intervalMappingSpace の VertexIso を作ること。評価後の閉同型を最終入力射間の比較とは扱わない。D-S の native 持ち上げとの接続に必要であり、チャットでも型と不足を明示報告する。
- D-S の追加必要条件（9716f3325）も確認。固定 ε core 内の可逆比較は各 null 対象上の実 cell 像の等号を要求する。したがって本件の評価後の同型を、そのまま ε core の path とみなさない。最終 intervalMappingSpace 比較の不存在を意味するとは主張しない。
- 六新葉を集約・専用監査・全体監査へ登録。Derived 集約14956 jobs、専用監査144宣言／16モジュール、全体監査26233宣言／2986モジュール成功、許容三公理のみ、終端0。import 閉包9170モジュール、循環・外部未コミット依存なし。最終固定辺の VertexIso の存在はこの検証に含めない。

### (a) 成立後の固定 cell・ε 商への持ち上げ手順（未着手）
- 待機条件：ユーザー指示により blocked を維持し、D-S の (a)（像対象の等号）の結果を待つ。以下は条件付き計画であり、最終 VertexIso の実装にはまだ着手しない。(a) が不成立ならこの経路を進めず、結果をユーザーへ報告する。
- 記号：P_A := DGCategoryCellResolution.Source R CA、S_A := resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)。CA／IA は切替済み固定 cone／入力。単位の比較対象は F := data(𝟙 A).resolved と G := id(P_A)、合成は F := data(f ≫ g).resolved と G := data(f).resolved.comp(data(g).resolved)。双方を同じ NullPreservingFunctorsε の対象として保持する。
1. (a) の公開定理の仮定・宇宙・適用範囲を確認し、各 b : S_A で F.obj b.val = G.obj b.val を単位・合成それぞれに取得する。元の二入力 f,g の比較に対する対象等号だけでは、data(𝟙 A) 対 id や data(f ≫ g) 対合成への適用を済ませたとしない。対象等号から射作用・ε 整合性は推論しない。
2. dgSuspensionUnitConeEvaluationIso／dgSuspensionCompositionConeEvaluationIso の成分と全 Hom 自然性を、充満な実加群評価を通して cone 自身の比較へ反映する。順逆・逆律と評価後の回収式を同じ成分で証明し、模型・代表・固定 data を変更しない。
3. 固定 comparisonFunctor 上の比較を構成する。cone 比較と固定 augmentation の可換条件を明示し、cell 生成射・微分・合成に対する全 Hom 自然性を検査する。単位は comparisonFunctor_identity、合成は comparisonFunctor_composition で右端を上記 G に厳密同定する。cone の自然同型から固定 cell 比較の存在を自動的に推論しない。
4. null 部分では手順1の対象等号を用い、比較の成分・逆成分・必要なホモトピーを固定 ε と整合させる相対条件を課す。恒等成分を選ぶ場合も、全 Hom 自然性・augmentation 比較と両立することを別途証明する。(a) は必要条件であり、この相対持ち上げの十分条件とは扱わない。未解決の整合条件が残れば、その型を公開してユーザー経由で D-S と照合する。
5. 厳密な閉比較を得られる場合は、順逆の単位複体パラメータについて quotientEpsilonCompatible を証明し、quotientEpsilonHomLift で同じ Hom 部分複体に入れる。逆律は元 Hom への mono 包含で反映する。H⁰ 同型／native 比較で構成する場合は、逆律を与える負次数パラメータ・境界も同じ ε Hom 内に持ち上げ、元 Hom 内だけのホモトピーで済ませない。高次相対 simplex を用いる場合も全 face・degeneracy と端点条件を検査する。
6. 得られた ε core 内の VertexIso を dgSuspensionQuotientNativeMap で写す。左端は dgSuspensionQuotientNativeMap_vertex、右端は同 Map_unit／Map_composition の全単体等号で、固定入力射の恒等／二本の合成へ厳密同定する。単位対象そのものの商則だけで固定 data の単位比較を代用しない。
7. 商 native Hom の比較を coherentHomIntervalComparison（必要な universe 移送を含む）へ写し、同じ二頂点を持つ intervalMappingSpace 内の比較にする。dgNativeMappingVertexEdge の回収式で両端の辺を照合し、DGSuspensionFixedUnitComparison／DGSuspensionFixedCompositionComparison を返す。端点の PerfDGInput は動かさない。最終 map の辺比較は既存 dgSuspensionEdgeIsoOfQuotientComparison に接続し、square／square_at の着手は従来どおり D-S の map 到着後とする。
- 各段で公開名・残る仮定をチャットでユーザーへ報告する。実装を再開した場合のみ対象 build・集約・専用／全体公理監査を実施し、所有パスを --only 指定してコミットする。今回の更新は計画のみで、(a) 成立や持ち上げの存在を主張しない。

### ∞ 圏側で非連結 K の関手性を取る設計の D 評価（実装未着手）
- 状態：D-S の disk 反例 f360d551b とユーザー指示に従い blocked を維持。工程2の全入力消費、固定 data の単位・合成 VertexIso、D-4 の全入力作用・square／square_at は凍結。前節の「(a) 成立後」手順も再開しない。以下は採否判断のための評価であり、∞ 側の新実装開始は意味しない。
- A：対象を dg 模型で計算し、関手性を正しい写像空間の StableInfinity で構成する原則に賛成。既存の厳密 dg 商関手圏の nerve に戻す条件は、新しい登録界面から外す。
- A 修正1：BGT Def.9.1 の cone は Fκ(C) := (Ind_ω C)^κ、懸垂はその Verdier 商。通常の Ind_κ(C) の κ-compact 部分と混同しない。既存 F2 の ind_stableCompactGeneration_unconditional κ C は同じ κ の Ind と compact 部分を扱うため、ω-Ind の κ-compact 部分を与える定理としてそのまま使わない。
- A 修正2：K が連結 K なら K(C) ≃ ΩK(Σκ C) を一般のスペクトル同値として仮定しない。構造射 K(C) → ΩK(Σκ C) を作り、反復 colim により非連結化する。非連結化後の K^nc(C) ≃ ΩK^nc(Σκ C) と区別する。Verdier 商の普遍性だけでは K の局所化定理は出ず、delooping の局所化証明・Fκ/Σκ の exact 列保存等を別工程に置く。
- A 修正3：現行 StableCategory／StableInfinity は冪等完備性をフィールドに含めない。全 StableInfinity 上で構成し Morita／冪等完備化不変性を証明するか、Cat_perf 部分と functorial Idem を用いるか、界面を統一する。Cat_perf 値の懸垂なら商の冪等完備化を明記し、raw 商と混同しない。
- 機構：HTT Cor.5.2.2.5 は、既にある Cartesian fibration の全遷移が左随伴を持つとき coCartesian にもなるという形で適用する。対象別の随伴存在だけで基底方向の全族を完成扱いしない。Ind_ω(f) の κ-compact 保存、κ-compact 部分の本質的小ささ・宇宙、包含 Id→Fκ の全自然性を明示する。S• から K∞ を作る際はスペクトル構造射・必要な Ω スペクトル化との整合も必要。
- B／D-8：I := dgKappaConeInput_unconditional' は projective・derivedFullyFaithful・kappaCompact・covers を全て保持する。したがって dgNerve(Cone_A) と D(A)^κ の比較同値を、compact 部分への因子化と充満忠実＋本質的全射から束ねられる。sphere-only 族の strict κ-small 直和閉性を新たに仮定する必要はない。covers は retract／telescope まで処理済みで、選択代表の strict 一致は要求しない。
- B／残る橋：K-B3 d4 の Ind_ω(νA) ≃ D(A) が元の perfect／Yoneda 包含を照合する全写像空間の同値であることを確認し、κ-compact 性の同値不変性で上記を Fκ(νA) へ移す。単なる hD(A) の三角同値や同じ κ の Ind 比較では不足。
- B／P・Z：P := dgKappaPerfectInput_unconditional' は isEquivalence と元の perfect 包含への全関手比較 inclusion を維持。Z := resolvedDGNullObjects の実安定閉包と dgKappaSuspension_isStableVerdierSequence を用い、νA→Fκ(νA) の包含を一致させてから Verdier 普遍性で対象ごとの商比較を得る。必要な Morita／冪等完備化は明示する。新模型を再変更する必要は現時点で見つからない。
- B／反復：各 A の一段比較だけでは K^nc_dg(A) ≃ K^nc∞(νA) は未完成。全 n の反復、同じ境界射・swindle による delooping 構造射との比較を Fun(ℕ,Sp) 内の同値として束ねて colim を取る。A 方向の厳密 dg 関手性は要求しない。登録は型どおり ν ≫ K^nc∞ とする。
- C／swindle：I.countableClosed、dgKappaConeCountableSum、dgKappaConeCountableSum_isExactFunctor、dgKappaSwindleInfinityIso を新 I にそのまま特殊化できる。固定 A での exact な可算和作用と id⊕T≃T は流用可能。一般の Fκ(C) の swindle は κ>ω の compact 閉性から別途構成し、加法性で K∞(Fκ C)≃0 を示す。D の固定 dg 証明だけで一般 C の全族の消滅を完成扱いしない。swindle 自体には可算和で足りる。
- C／流用境界：I/P/Z・新 stage provider・covers・固定 A の swindle／商列を保持する。既存 Morita／P native 族は補助比較に使えるが、構成した Fκ 作用との全単体一致は新たに照合する。今回確認した F1 の left/right straightening 分類は空間値であり、Cat∞ 値の一般 (co)Cartesian 分類の代用品とは扱わない。F2 の対ごとの随伴選択も基底を動かす全族との整合確認が必要。
- C／凍結：ε 圏／quotientInputFunctor／商の厳密単位合成則は既存の正しい下位補題として残す。固定 data への全入力持ち上げ・最終 VertexIso・D-4 の旧仕様は追わない。D-8 本体、対象ごとの I/P/Z 比較、swindle は凍結対象から除く。旧計画・未供給型を削除せず、旧経路の成果を新経路の完成と数えない。
- D／粗見積り：必要な ∞ 側界面が揃った後の D 所有接続は、cone の compact 比較1–2日、P/Z と商比較1–2日、swindle 照合0.5–1日、反復列・構造射・colim 比較2–4日、合計およそ5–10実働日。一般 Ind／Calkin の全族・K∞・局所化定理が未供給なら別見積りで、数日–数週の追加リスク。現時点で全体完了期限は確約しない。
- E／主リスク：ω と κ の取り違え、raw 商と冪等完備商の混同、スペクトルの連結切断、反復列の構造射比較、宇宙、普遍性から局所化を循環的に仮定すること。現行 IsLocalizingInvariant は零保存＋全 Verdier 四角形の fiber 性であり、BGT の意味での filtered-colimit 保存も主張するなら別に証明する。
- E／代替：既存の Pr^L と compact 生成の関手的普遍性から Fκ を直接構成できれば、一般 Cat∞ 値 straightening 全体の新規実装を先行条件にしない。W1 の Fun(ℕ,Sp) 直接構成も、正しい ∞ 写像空間で全整合を証明する限り有効。いずれも旧 dg 商関手圏への strict 持ち上げを再要求しない。
- 参照：BGT §9.1、Def.9.1／9.6、Lemma9.4、Prop.9.5（https://msp.org/gt/2013/17-2/gt-v17-n2-p03-s.pdf）；HTT Cor.5.2.2.5（https://www.math.ias.edu/~lurie/papers/HTT.pdf）。評価はチャットでもユーザーへ渡す。今回は計画更新のみで Lean 本体を変更しない。

### 先行 B1：固定 cone と実導来圏の κ-compact 部分
- ユーザー割当：∞ 側の Ind／Calkin 界面を待たず、対象別 B1 を先行。最終 VertexIso・D-4 後半の凍結は維持する。
- 新規葉 Compact/ConeDerivedEquivalence：任意の I : DGKappaConeInput R D κ に対し dgKappaConeCompactComparison を定義。I.kappaCompact で実導来比較を F2.Compact.kappaCompactObjects κ D(D) へ因子化し、包含後は元の dgKappaConeDerivedComparison と全単体で厳密一致（inclusion）。
- 同 comparison の isFullyFaithful は I.derivedFullyFaithful と全部分包含の相殺、isEssentiallySurjective は I.covers と全部分包含の preimageVertexIso で証明。dgKappaConeCompactEquivalence は順方向を comparison に固定し、逆比較の inclusion も元の compact 包含との FunctorIso として回収する。
- 新規葉 KappaPerfect/SphereClosureCompactComparison：新 dgKappaConeInput_unconditional' への特殊化 dgKappaSphereClosureCompactComparison／dgKappaSphereClosureCompactEquivalence を公開。equivalence_hom で順方向を厳密回収。対象別の QCatEquivalence であり、Ind_ω 比較・新模型の全入力作用を仮定しない。
- 流用範囲：新 I.countableClosed は同じ実加群の可算直和への閉性。dgKappaConeCountableSum と dgKappaSwindleSource は新 I にそのまま適用できる。dgKappaSphereClosureCountableSum_isExactFunctor／dgKappaSphereClosureSwindleInfinityIso は、既存の完全性／全関手比較をその新 I に特殊化して公開。対象・代表・収縮を取り直さない。
- 流用の限界：一般 C の Fκ(C) の可算和・swindle 族、K∞ の加法性・消滅、入力 A 方向の自然性、Ind_ω への比較はここで供給しない。compact 部分への swindle の移送は得られた同値を用いる後続工程とし、B1 の完成と混同しない。
- B1 検証：新 I 特殊化の対象 build10453 jobs、Derived 集約14959 jobs、専用監査163宣言／18モジュール、全体監査26254宣言／2988モジュール成功。許容三公理のみ、終端0。新二葉の import 閉包6656モジュール、循環・外部未コミット依存なし。対象別 B1 を供給済みとし、一般 Ind／Calkin への接続と旧 D-4 凍結は区別して維持する。

### R2-B 読み取り専用調査
- 先行B1完了後に着手。処置案・全件分類は refactoring-infinity-r2-b.md と archive/r2-b-classification-2026-10-27.json。Leanソース・集約・監査は変更せず、実施はR2-A/C/Dとの合意後の停止窓に限定する。
- DG555の552はscripts/audit/dg.leanの直接importであり、top-level監査のみの被覆集計と区別。DGは登録488/archive67、HomotopicalAlgebra123は登録1/archive1/旧互換入口削除候補121、凍結41は診断14/archive20/主経路保持5/比較再利用2と分類。一般bar5本とB1・I/P/Zを保持する。
- 指定209逆辺・141 import先と全678未登録葉・凍結41本を記録。R28/R31/R32/R34とaugmentation旧53組の対応表を用意し、旧4組の消滅を識別。計画だけでなくチャットでユーザーへ処置案を報告する。

### K-S• 先行依頼：perfect-projective 加群の像（型確認待ち）
- 依頼 /tmp/ks-realization-perfect-request.lean を確認。提案は追加仮定なしの元の型：任意の T : DGFunctor R (RightModule R D) (RightModule R E) が全 representable を modulePerfectProjectiveOver R E Set.univ へ送れば、全 perfect-projective 加群を同じ性質へ送る。
- 判断根拠：任意の加群値 dg 関手について dgModuleFunctorShiftIso／dgModuleFunctorConeIso が既存。閉射関手の加法性による有限和保存と onHomotopy の retract 保存も使える。通常の関手と異なり、今回の dg 関手にこれらの保存性を追加入力する必要はないと判断する。全 quasi-iso 保存や左随伴性も仮定しない。
- 証明予定：既存 Morita.perfectDGFunctorImage_projectivePerfect で導来 perfect 性を得る。h-projective 性は有限 cell の生成操作に関する帰納で像について証明し、源 M の h-projective 性を使って導来 retract をホモトピー圏の retract に持ち上げる。T.onHomotopy で送り、moduleHomotopicallyProjective_of_homotopyRetract（または projective locus の retract 閉性）で戻す。導来 perfect 性だけから像の h-projective 性は推論しない。
- 公開予定名 SerrePositivity.DifferentialGraded.Morita.perfectDGFunctorImage_perfectProjective。新規葉 DifferentialGraded/Morita/PerfectProjectiveImage（予定）。KST import を加えず既存 DG 正本 API を使う。dgPerfectRealization にも元の hgen をそのまま適用する方針で、T = dgModuleExtension への制限は不要案。
- ユーザー経由で K-S• にこの型を確認中。本体・証明・集約変更は確認回答後に着手する。見積りは確認後2–4時間（実装・対象build・公理監査）。旧 D-4／最終 VertexIso の凍結は維持する。

- K-S• 確認回答：元の依頼型・追加仮定なしで本体へ進むことをユーザーが承認。新葉 Morita/PerfectProjectiveImage に perfectDGFunctorImage_projective_finiteCell／projective／perfectProjective を構成。有限 cell の像の全 Hom 射影性、源の射影性で持ち上げた実ホモトピー retract、既存の導来 perfect 保存を組み合わせる。
- 対象 build2741 jobs成功。KST import のない DG 正本葉として公開し、Derived 集約・全体監査へ登録。専用 audit_dg_perfect_projective_image は全自作宣言の公理閉包と元の全称依頼型（独立した u/v/w、追加仮定なし）を検査する。旧凍結経路は変更しない。
- 最終検証：対象2741 jobs・Derived集約14960 jobs成功。専用監査は新葉の全3宣言について許容三公理のみ、元の全称型照合も成功、終端0。依存閉包551モジュール、循環なし・KST依存0・外部未コミット依存なし。公開型は元依頼のままで、全体監査への登録も追加した。

### K-S• 上指定 S 二単体：加群の明示境界のみ
- ユーザー指定により一般 DGFunctor の Hom end 比較には着手しない。新葉 DifferentialGraded/Derived/ProjectiveContraction の moduleHomotopicallyProjective_contractingElement_of_acyclic は、h-projective かつ moduleAcyclic な任意の右加群について ∃ H, d H = unitElement を供給する。既存 complexAcyclic_boundary を実 Hom end に適用し、KST import を加えない。
- Derived 集約・全体監査へ登録し、専用 audit_dg_projective_contraction で全自作宣言の公理閉包と元の公開型を検査する。固定 Γ の bimodule 射影性・関手 Hom end への移送は未供給のまま。完了後は停止準備完了に戻る。
- 検証完了：新葉と Derived 集約の対象 build14962 jobs成功、専用監査は全1宣言について標準三公理のみ・依頼型照合成功（終端0）。新葉のローカル依存閉包58モジュール、循環なし・KST依存0。全体監査は登録のみで再実行せず。加群版の供給完了後、停止準備完了。

### K-S• 第2件：native dg nerve の同値から準同値の反映
- (b) は既存 dgStableHomotopyEquivalence_naturalityIso と h の比較同値・圏同値の相殺で H⁰ の圏同値を回収可能。(c) の既存逆向きは dgH0IsoOfVertexIso。(a) の一般形は新葉 DGPretriangulatedGradedShift に dgPretriangulated_gradedShiftWitness として供給：shifted representable のホモトピー表現可能性・全次数 Yoneda 同型から閉斉次射と片側単位の境界原始元を取る。
- 新葉 DGNerveReflectsQuasiEquivalence に dgFunctor_onHomotopy_isEquivalence_of_nerve／dgFunctor_homQuasiIso_of_nerve／dgFunctor_quasiEquivalence_of_nerve を公開。始域だけ Small・前三角、標的の Small・前三角は不要。ユーザー指定の8h以内・KST importなしの範囲で供給へ着手した旨と既存名・見積り4–8hをチャットで報告済み。固定 Γ の自然収縮・旧D-4凍結には着手しない。
- 検証完了：対象二葉・Derived集約14964 jobs成功。専用 audit_derived_dg_nerve_reflection は新二葉の補助宣言を含む全6宣言の公理閉包を検査し標準三公理のみ、依頼の u+1 全称型と標的 Small 不要の型も成功（終端0）。依存閉包928モジュール、循環・KST依存・他レーン未コミット依存なし。Derived集約と全体監査へ登録（全体監査は再実行せず）。準同値まで供給完了後は停止準備完了。
