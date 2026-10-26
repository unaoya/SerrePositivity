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
- 正本：`kst-lanes/L10-nonconnective.md` 100–110・144–148行。
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
- 採用二葉の対象 build 11300 jobs成功。専用監査43宣言／2モジュール、許容三公理のみ、終端0。Derived 集約14900 jobs成功。局所 import 閉包11173モジュール、循環なし。全体監査は実行中。
