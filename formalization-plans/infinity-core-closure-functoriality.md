# D-S：閉包の実延長と懸垂作用

更新：2026-10-27。D と並行。担当は D-3、D-4a。

## R 窓前の停止位置・再開入口

現在地：`2c91afa4f4b078e8eee5670a81d45744470f4ea6`。ユーザー指定により工程 1 は停止。
残りは R 窓後の ∞ 側パッケージへ移管。新しい Lean 作業を始めず、R2-B（`b53587371`）由来の R 窓割当を待つ。
凍結候補（ε 経由）には触れない。CoherentStage* は凍結不可。以下の旧工程記録は経緯であり再開指示ではない。

| 未証明項目 | 実作業時間の見積り | 再開条件・範囲 |
|---|---:|---|
| 新 Σ∞(ν f) と固定降下の模型比較 | 8〜24 時間 | Indω–導来圏・Yoneda／包含・商三角形の供給後 |
| ν と固定 K の照合 | 16〜32 時間 | 対象値と反復列の構造射を含む図式比較。入力自然性は次項 |
| 全高次整合 | 40〜80 時間以上 | Ind・商・K の族構成。最も不確実 |
| 採用境界の空性 | 調査 4〜8 時間、決着は見積不能 | 未証明のまま保留。必須工程から除外 |

新経路は前提の供給後に計 64〜136 時間以上。共有ビルド・供給待ちは除く。
検証済み区切りは現在地そのもの。次の固定 A・B・f の模型比較区切りは供給後 8〜24 時間。
再開入口（namespace `SerrePositivity.InfinityCategories`）：
`dgSuspensionQuotientTriangle`、`dgSuspensionQuotientUniversalDescentComparison`、
`dgSuspensionQuotientLiftedPrecomposition_isFullyFaithful`、`dgSuspensionQuotientLiftedTriangle`、
`dgSuspensionQuotientModelComparison`、`dgSuspensionQuotientConeModelComparison`。
必要な供給型：m=max(u+1,v)、U=uliftFunctor（各型に必要な大きい宇宙への持ち上げ）として、
`QCatEquivalence (dgKInputIndCompletion R A) (U.obj (dgModuleDerivedInfinityCategory R A))`
と元の perfect 包含／Yoneda との FunctorIso。これを κ-compact 部分へ制限した cone 比較 cA・cB と、
qA・qB＝固定商射影、a・b＝新懸垂模型への比較、pA・pB＝新射影、L＝新 cone 射、G＝Σ∞(ν f) に対する：
```lean
FunctorIso (U.map qA ≫ a) (cA ≫ pA)
FunctorIso (U.map qB ≫ b) (cB ≫ pB)
FunctorIso (U.map (dgNerve.map d.cone) ≫ cB) (cA ≫ L)
FunctorIso (pA ≫ G) (L ≫ pB)
```
これらの存在は未証明。上記公開入口で固定 Q(data f) の比較へ接続する。
再検証完了：所有 57 ファイルは現在地コミットと一致。現共有依存下で両独自集約のビルド・専用監査に成功（53 葉・770 宣言、終了コード 0）。Lean／凍結候補の変更なし。

## 所有境界

- `SerrePositivity/InfinityCategories/Derived/ClosureFunctoriality/` の新規葉と独自集約。
- `SerrePositivity/InfinityCategories/Derived/SuspensionAction/` の新規葉と独自集約。
- `scripts/audit_derived_closure_functoriality.lean` と本計画（300 行以下）。
- Derived のその他の既存ファイル、および KST は読み取り専用。
- 共有集約・共有監査・共有計画には登録しない。

## D-3：基底非依存の f_! 関手化

状態：自然比較・集約ビルド・独自公理監査を完了。最新の検証数は末尾を参照。

実装済みの葉：

1. `StrictRange`：`dgModuleStrictRange` は固定実代表集合の閉零同型による飽和。
   shift・二項和・全閉零次射の cone・可算和に沿う閉性。
2. `ExtensionRange`：`dgProjectiveClosureStage_extension_strictRange`。
   基底像の実同型互換を、元の超限閉包の帰納原理で全段へ伝播する。
3. `FamilyImage`：`dgProjectiveClosureFamily_extension_image`、
   `DGProjectiveFamilyImage`、`dgProjectiveClosureFamilyImage`。
   添字写像 φ と対象別の実 dg 同型を保持する。
4. `FullFunctor`：`DGModuleStrictImage`、`.ofRange`、`.functor`、`.functor_map`。
   元の全 Hom 鎖写像を実比較同型で共役し、map_id・map_comp を厳密に保持する。
5. `ClosureFunctor`：`dgProjectiveFamilyObjects`、
   `DGProjectiveFamilyImage.strictImage`、`dgProjectiveClosureFunctor`。
   同じ像集合の充満部分 dg 圏間の実作用。
6. `SphereFree`：`dgKappaSphereFreeExtensionIso`、
   `dgModuleExtensionSphereCoproductIso`。
   既存の sphere・余積比較から、同じ ordinal と次数の基底互換を供給する。
7. `ModuleExtension`：f_! 専用入口
   `dgModuleExtensionClosureFamilyImage`、
   `dgModuleExtensionClosureStrictImage`、`dgModuleExtensionClosureFunctor`。
   余極限保存は延長–制限随伴で証明し、呼び出し側には要求しない。
8. `Perfect`：`DGModuleStrictImage.preservesPerfect`。
   射影的源の恒等射影分解による実延長計算と導来 perfect 保存を使用する。
9. `ImageLaws`：指定実比較データの `.id`、`.comp`、`.comp_map`、
   `.id_functor`、`.comp_functor`。
   合成は比較同型を写して連結する。独立な再選択には頼らない。
10. `SphereClosure`：`dgKappaSphereClosureExtensionStrictImage`、
    `dgKappaSphereClosureExtensionFunctor`。D-2 の objects 集合へ特殊化。
11. `SuspensionAction/ConeData`：
    `dgModuleStrictImageSuspensionMapData`、`_cone`、`_augmentation`。
    固定 cone 間の strict image を正本 `DGKappaSuspensionMapData.ofConeFunctor` へ送る。
12. `Comparison`：`DGModuleStrictImage.comparison_naturality`、
    `.comparisonIso`、`.comparisonIso_hom_app`。元の実延長と代表評価の
    全 Hom 自然な同じ比較同型を、閉零自然同型へ束ねる。
13. `SuspensionAction/SphereConeData`：
    `dgKappaSphereClosureSuspensionMapData`、`_cone`、`_preservesPerfect`、
    `dgKappaSphereClosureSuspensionInputMap`。D-2 のコミット済み新 cone 間の
    strict data と正本入力射を具体化。段提供者は選ばない。

### 公開入口の仮定

`dgModuleExtensionClosureFunctor R C D F hT B E hB`：

- 任意の dg 圏 C、D と dg 関手 F。
- u-small な対象型、任意の射影的基底 B、E。
- 共通の well-founded linear order T と Nonempty T。
- hT：可算個の段階に共通の真の上界がある。
- hB：各 B_i の実延長が、ある E_j と閉零射圏で同型。
結論は `Set.range` の充満部分 dg 圏間の厳密 dg 関手。
関手内部の恒等射・合成保存と、入力 F 自体に関する作用の coherence は別物。
独立な Classical.choice の選択が入力の恒等・合成と厳密一致するとは主張しない。固定収縮補正の保存：`8bf395f1b99133cd0b1bf6ffca3635e675755b89`。

## D-4a：全入力作用

状態：D-2 `4cd747153` と K-B3 の切替 `354e05773` を受領。D-4a を再開。
採用提供者：`KST.NonConnective.dgKappaUnconditionalStageProvider R κ hκ`。
`dgKappaUnconditionalStageProvider_cone_newInput` によって cone は D-2 の新入力と rfl で一致。
実装した追加工程：

- `SuspensionAction/UnconditionalData`：`dgSuspensionUnconditionalMapData`、
  `_cone`、`dgSuspensionUnconditionalInputMap`。
  data の値は `dgKappaSphereClosureSuspensionMapData R A B f.down κ hκ` そのもの。
- `ClosureFunctoriality/Parameter`：`DGModuleStrictImage.parameter`、`.parameter_app`。
  任意の複体パラメータの全次数変換を固定代表間へ共役する。
- `ClosureFunctoriality/InputParameter`：`dgKappaSphereClosureExtensionParameter`、
  `dgKappaSphereClosureExtensionInputHom`、`_π`。
- `ClosureFunctoriality/InputFunctor`：入力 Hom の縦方向の単位・合成保存と、
  `dgKappaSphereClosureExtensionInputFunctor`。
- `ClosureFunctoriality/NativeHom`：`dgKappaSphereClosureNativeHom`、`_vertex`。
  入力関手圏の native Kan core の全単体を cone 関手圏へ送る。
- `SuspensionAction/QuotientParameter`：`dgSuspensionMapContractedFunctor`、
  `dgSuspensionQuotientParameter`、`_epsilon_necessary`。
  正本 data の同じ resolved 射と選択 ε を使う、全次数変換の商への延長入口。
  同じ成分を保持する厳密延長に ε 整合が必要なことも証明する。
- `ClosureFunctoriality/ContractionComparison`：
  `dgContractionCommutatorPrimitive_d`、`dgGradedContractionPrimitive_d`、
  `_d_of_closed`、`_map`。二つの固定収縮の交換差を境界で制御する。
  任意次数では入力の微分項も保持し、dg 関手との厳密可換性を証明。
- `SuspensionAction/QuotientContractionComparison`：
  `dgSuspensionContractionCorrection`、`_d`。正本 data の同じ ε に特殊化。
  境界であることは厳密な ε 整合の代用ではない。
- 旧 cell／固定 ε の全入力経路の供給調査は完了。後述の反例により凍結。
- `ClosureFunctoriality/CellGenerators`：`dgCellCycleSphere`、
  `_augmentation`、`_comparison`、`_comparison_element`、
  `dgCellComparisonHom_initialNaturality_mapped`。最終分解内の初期生成元の
  比較像と、全次数 native Hom が満たす厳密な自然性を明示する。
  `_unitGeneratorNaturality` は単位ラベルの初期生成元での必要条件。
- `ClosureFunctoriality/ChoiceInvariant`：
  `dgProjectiveClosureFamilyImage_index_eq_of_iso`、
  `dgProjectiveClosureFunctor_obj_eq_of_iso`。raw 像が対象別に実同型なら、
  選択述語の外延性によって D-3 の添字・対象選択が厳密一致する。
  Hom 作用・選択比較同型の一致や ε 整合は、ここからは結論しない。

### 旧 ε 経路の再分担（履歴）

固定 ε 商の作用は D に移管・供給受領済み。一般作用は D の二対象反例で不採用、ε core 経由も後述の反例で閉じた。

### 工程 1 の dg 供給型に対する形式化済み反例

- `CellDegreeSplitting`：`dgCellStageZeroRetraction_split`。
  各次数で最終分解から初期段への加群射の分裂を構成。鎖写像とは主張しない。
- `CellUnitNonzero`：`dgCellResolution_unit_ne_zero`。
  非零係数環上で、分解先の全対象の厳密単位は鎖の元として非零。
- `CellZeroObstruction`：`no_dgCellComparisonInputFunctor`、
  `no_dgZeroInputFamily`。一対象・全 Hom 零の dg 入力では、
  入力関手圏の単位変換が零。dg 関手で評価した分解先の非零単位と矛盾する。
- `SuspensionAction/ResolvedZeroObstruction`：
  `no_dgSphereClosureResolvedInputFunctor`。D-2 の同じ新 cone へ特殊化。
  終域を固定 ε 整合 Hom へ制限しても、忘却と評価で同じ矛盾が出る。
- 従って、全入力の `resolvedInputFunctor : DGFunctor ...` という供給型は不可。
  native Kan core 間の全単体 SSet 射や、元の最終 map の非存在は未証明。
  工程 1 を native SSet 射として直接供給する型への変更をユーザーが採用。
  候補は入力 native core → ε 整合関手圏の dg nerve の core。
  対象作用・固定模型・最終 map と edgeIso の目標・新仮定なしを維持する。
  候補の一般の存在は未供給。dg 反例は R 候補として独自集約・独自監査に留め、
  主経路の集約には登録しない。
- `CellZeroNativeSeparation`：`dgCellZeroNativeHom`、`_vertex`。
  零入力では同じ comparisonFunctor の頂点を持つ全単体 SSet 射が存在する。
  上記 dg 反例と native SSet の問題を区別する診断であり、任意入力の完成ではない。

### D の工程 2 の消費型（native core）

D の公開 `6b698006a`・`960649fc1` を採用。
D の `quotientInputFunctor` に `dgNerve.map` と `quasicategoryCoreMap` を適用する。
`coherentNerveMap` は工程 3 の全 Hom の単位・合成を確認した後で使用する。
必要な native 射は次の形（C、D、S、T は固定）：
```lean
(quasicategoryCore (dgNerve R (NullPreservingFunctorsε R C D S T)) : SSet) ⟶
  dgFunctorNativeMappingSpace R
    (DGQuotient.QuotientObject C S) (DGQuotient.QuotientObject D T)
```
その値は `quasicategoryCoreMap (dgNerve.map (quotientInputFunctor R C D S T))`。
対象 F の頂点は、同じ `quotientDGFunctor R C D F.val S T F.property` の頂点へ送る。
D の ε Hom は元の dg 部分複体の定義のままでよい。D-S は入力 native core から
この ε core への全単体射を構成する。頂点別の ε 整合だけで全単体の着地を推論しない。
D 側の native 忘却は `quasicategoryCoreMap (dgNerve.map
(nullPreservingFunctorsεForget R C D S T))`。固定頂点の照合と全単体の着地の確認に使う。

- 実装 `SuspensionAction/QuotientNative`：`quotientNativeInputMap`、
  `_vertex`、`quotientNativeInputForget`、`_vertex`。D の現行型だけで構成済み。
  D の native 正本を import し、重複名を解消。`quotientNativeInputMap_unit` は
  同じ全単体の単位保存を D の `quotientEpsilonNativeMap_unit` から得る。
- 実装 `SuspensionAction/NativeTarget`：`dgSuspensionResolvedEpsilonCore`、
  `dgSuspensionResolvedEpsilonObject`、`dgSuspensionResolvedEpsilonVertex`、
  `dgSuspensionQuotientNativeMap`、`_vertex`。切替後の段提供者の正本 data に一致。
- 主経路集約 `SuspensionAction/NativeAll` は反例・診断を import しない。
  独自全体集約 `All` と独自監査には R 候補も保持する。
- 未構成の工程 1 は `dgFunctorNativeMappingSpace R A B` から
  `dgSuspensionResolvedEpsilonCore R κ hκ A B` への全単体射。
  頂点の厳密一致を使う経路と、指定 native 比較で照合する経路を区別する。
  最終 map の対象頂点の厳密等号は変更しない。

### native 持ち上げの組立（存在証明と区別）

- `ClosureFunctoriality/NativeSimplexLift`：次数別単射な Hom に沿う
  `dgNerveSimplexOfMappedData` と `dgNerveMapLift`。候補成分の像が既知の単体なら
  方程式を反映し、各単体の持ち上げから面・退化の自然性を回収する。
- `SuspensionAction/EpsilonSimplexLift`：D の ε Hom 包含に適用。
  `quotientEpsilonNerveLift`、`quotientEpsilonCoreLift` と各 `_forget` は全単体等号。
  `quotientEpsilonElement_factor_iff` は任意次数の成分の所属を、D の
  disk パラメータに対する `quotientEpsilonCompatible` と同値にする。
  前提は実際の全成分の ε 持ち上げであり、任意入力での成立は未証明。
- D の `0263f71c9` の横合成を固定模型に特殊化：
  `dgSuspensionResolvedEpsilonComposition`、`dgSuspensionQuotientNativeMap_composition`。
- 接続点 `dgSuspensionNativeHom_vertex`：工程 1 の厳密頂点式から、商消費後も
  同じ `dgSuspensionUnconditionalInputMap` の native 頂点になることを証明。
- edgeIso の準備は D に移管（ユーザー指示）。D-S は工程 1・ε 着地・map を担当。
  map が出来たら先に公開し、上記 Hom 作用と map の辺の関係をユーザー経由で D へ報告。

### 厳密豊穣経路の単位の必要条件

`SuspensionAction/NativeUnitRequirement` を独自 All・監査に登録（主経路には未登録）。
`dgSuspensionResolved_identity_of_nativeUnit`：固定 data の頂点作用と厳密な
ε core 単位保存が揃うなら `data (𝟙 A).resolved = DGFunctor.id _` が必要。
`dgSuspensionCone_obj_identity_of_nativeUnit`：cone の恒等入力も全代表を動かせない。
`ChoiceInvariant` の入力二代表に関する選択不変性も証明。
`dgSuspensionCone_eq_of_iso_of_nativeUnit`：この厳密単位経路は、元の cone 代表の
実加群同型に関する骨格性まで要求する。代表集合の非骨格性は未証明。
`dgSuspensionCone_eq_of_iso_of_resolvedIdentity` は data 自体の resolved 恒等性から同じ骨格性を導く。
現在、この必要等号の成立は未証明。D の商の単位則だけでは導けない。
一般の map の不存在は示していない。採用目標の edgeIso は厳密な辺等号を要求しない。
D に恒等入力の実商関手と懸垂の恒等関手の比較も照会中（ユーザー経由）。
主経路 `dgSuspensionNativeHom_vertexIso` は、工程 1 の頂点を ε core 内の
指定 VertexIso で照合する場合、同じ商の native Hom 内へ比較を送る。
この比較と map の辺の関係は map 構成時に D へ報告する。比較の存在は未証明。
`NativeIntervalIso`：`dgNativeInputMapIsoToInterval`／`dgIntervalInputMapIsoToNative` は、
同じ通常射の native 頂点同型と端点固定 interval 同型を両方向に移す。
`NativeActionRequirement`：最終 action の `nativeIsoOfNativeIso` は、ε を経由せず
固定実商関手間の native 同型を回収する（辺比較は VertexIso のまま）。
`nativeDiskSuspensionComparisonType`／`nativeDiskSuspensionComparisonOfAction`：零／disk 対で最終 map に必要な出力比較。
この出力比較の存在・不存在は未証明。主経路への診断葉の追加なし。
D の `b8086c72c` は恒等・合成を実加群評価後の閉同型で比較。固定 cell／ε の接続は未供給。
D の `a71c35749` の `dgSuspensionEdgeIsoOfQuotientComparison`／`_OfQuotientEdgeEq`
は最終辺から商作用辺への比較を消費する型で一致。最終辺比較の実例は未供給。

### 固定 ε Hom の成分の必要条件

`EpsilonCellRigidity` を独自 All・監査へ登録（主経路への追加なし）。
`quotientEpsilonCellParameter_component_zero`：標的が `Source R D` の場合、
ε 整合パラメータの各 null 対象 b での成分は、次数 q ≠ 0 または像対象が異なれば零。
`quotientEpsilonCellHom_component_zero_of_degree_ne_zero` は正本 ε Hom への適用。
`quotientEpsilonCell_unit_not_boundary`：非零環かつ null 対象があるなら、
ε 関手圏の単位は同じ ε Hom 複体内で境界にならない。標的 cell の H⁰ については未主張。
証明は単一 ε 語の分離・tensor の二次数分離・cell 単位の係数 1 による消去。
`EpsilonCellHomotopy`：次数 −1 の消滅で評価は H⁰ から厳密な閉射へ降下。
`quotientEpsilonCell_obj_eq_of_coreVertexIso`：非零環上、ε core 内の VertexIso は
各 null 対象で同じ実 cell 対象を要求する（同型だけでは足りない）。
`quotientEpsilonCell_nativeMap_obj_eq`：入力の可逆比較を持つ両端について、
ε core への全単体射と頂点の指定比較があれば、同じ像対象等号が必要。
頂点一致を ε core 内の同型へ弱める経路にも適用。独自 All・監査のみ登録。
`NativeEpsilonRequirement` の `dgSuspensionResolved_obj_eq_of_nativeHom` は固定 resolved 族への特殊化。
`dgSuspensionResolved_obj_eq_iff_extensionIso`：指定対象の等号は、選択前の実延長像の同型と同値。
`RepresentableSeed`：固定 sphere-free 基底内の一セル代表と、各代表加群との実同型。
`NativeRepresentableRequirement` の `dgSuspensionInputObjectIsoOfNativeHom`：工程 1 と ε core 内の
頂点比較があれば、入力側の可逆比較は各元対象の実閉射同型を要求する。H⁰ 同型では足りない。
独自 All・監査のみ登録。`PointFamily` は一対象環からの対象関手の全 Hom 作用、
`NativeCoreIso` は H⁰ 同型を同じ core の頂点比較へ移す検証用の入口。
`NativeDiskPair`：零と非零可縮 disk の有限入力。二つの点関手は入力の native Hom 内で可逆。
`NativeEpsilonDiskObstruction` の `nativeDiskResolvedSeedImages_ne`：指定一セル null 対象で
同じ sphere-closure data の resolved 像が異なることを証明（(a) の具体的反例）。
`no_nativeDiskSuspensionEpsilonHom`：固定頂点を ε core 内で比較する工程 1 は存在しない。
比較付き頂点でも不可能。主経路未登録。最終 map 自体の不存在は未主張。
残る map は ε core を経由しない経路が必要。Fun∞ 側の商作用から固定出力 native Hom への橋は未供給。
頂点は `dgKappaSuspensionKInput R A (s A).cone`。cone の全 Hom 作用で最終作用を代用しない。
最新判定：`NativeActionNonemptinessBoundary` を独自集約・監査に登録。
`DGSuspensionCoherentActionInput.data` は固定 sphere data との一致を要求しない。
`nativeDiskCommonDataComparison`／`not_nativeDisk_all_admissible_data_separated`：同じ許容 data に自己同型。
`no_nativeDisk_fixedData_action_of_no_comparison`：最終比較型の空性が得られた場合の条件付き否定。
その前提 `¬ Nonempty (nativeDiskSuspensionComparisonType R κ hκ)` は未供給。
ε core での非存在を最終商関手圏での非存在へ移す推論は未供給。bare 採用境界の空性は未証明。
既存 `nativeDiskSuspensionComparisonOfAction` は端点固定 edgeIso を既に考慮する。
StableInfinity 案の評価（設計検討のみ。quasi-functor／bimodule の実装は開始しない）：
BGT Def.9.1 の cone は Fκ(C)=(Indω C)^κ。Indκ(C)^κ へ置き換えない。Cat^perf を標的とするなら Σκ(C)=Idem(Fκ(C)/C)。既存 Verdier 列には完備化がない。
連結 K の ΩK(ΣC)≃K(C) は一般には不可。連結被覆の比較と非連結化を区別する。局所化不変性は Verdier 普遍性だけでなく、完全列保存・filtered colimit 保存の証明が要る。
HTT 5.2.2.5 は既存 Cartesian 族の遷移が左随伴を持つ場合の共変化に使う。入力ごとの随伴の選択だけで全高次整合を得たとは数えない。κ-compact 保存も別照合。
剛性は ε core のもの。ν による quotient 出力二辺の比較の非存在を意味しない。数学的経路：cone の比較を quotient 普遍性の全完全関手圏の充満忠実性で降下する。
`StableQuotientTriangle`：`dgSuspensionQuotientTriangle` は既存正本の三角形を保持。`dgSuspensionQuotientUniversalDescent` は完全商普遍性から独立に構成し、`dgSuspensionQuotientUniversalDescentComparison` で固定 Q(data) と同定。独自集約・監査のみ登録。
D-3・perfect 保存・strict data は対象別 cone／商と評価比較に流用できる。native cone 比較は quotient 前で流用。ε 消費射を StableInfinity の全 Hom 作用と扱わない。
対象別に必要：ν(Σdg A)≃Σ∞(ν A)、さらに反復 Sp 図式全体の同値（構造辺との可換性を含む）。段ごとのスペクトル同値だけでは旧 dgNonconnectiveK の余極限比較に足りない。
新登録関手の対象値の照合には A ごとの図式同値でよい。旧射作用の照合には A での自然性も要る。W1 の 2-cell を個別に選ぶだけで全単体関手と数えない。全高次整合を供給する。
`StableQuotientModelComparison`：宇宙持ち上げ後の全前合成の充満忠実性・固定三角形と、`dgSuspensionQuotientModelComparison`／`dgSuspensionQuotientConeModelComparison` を構成。cone 比較・射影三角形・cone 射の自然性・新商の降下三角形から固定商射の比較を回収。新 Σ∞・これらの供給・ν と固定 K の照合・全高次整合は未証明。固定 native 比較型／bare 境界の空性も未決。

## 検証

独自集約：`ClosureFunctoriality/All.lean`、`SuspensionAction/All.lean`。
両独自集約のビルド成功。監査は 53 葉・770 宣言で成功。主経路 `NativeAll` は変更なし。
独自監査は全宣言を走査し、許可公理を `propext`・`Classical.choice`・`Quot.sound` に限定。
`sorryAx` は不許可。共有監査は編集しない。検証コマンド：
```sh
lake build SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.All SerrePositivity.InfinityCategories.Derived.SuspensionAction.All
lake env lean scripts/audit_derived_closure_functoriality.lean
```
