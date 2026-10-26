# D-S：閉包の実延長と懸垂作用

更新：2026-10-27。D と並行。担当は D-3、D-4a。

## 所有境界

- `SerrePositivity/InfinityCategories/Derived/ClosureFunctoriality/` の新規葉と独自集約。
- `SerrePositivity/InfinityCategories/Derived/SuspensionAction/` の新規葉と独自集約。
- `scripts/audit_derived_closure_functoriality.lean` と本計画（300 行以下）。
- Derived のその他の既存ファイル、および KST は読み取り専用。
- 共有集約・共有監査・共有計画には登録しない。

## D-3：基底非依存の f_! 関手化

状態：自然比較を含めて実装・集約ビルド・独自公理監査を完了。
D-2 の具体化を含む 13 葉・115 宣言の公理監査が終了コード 0 で通過。
D-4a の cone 全 Hom 作用と商パラメータ入口まで、19 葉・161 宣言の
公理監査が終了コード 0 で通過。両独自集約のビルドも成功。

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
独立な Classical.choice の添字選択が F の恒等・合成と厳密一致するとは主張しない。

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

頂点は必ず `dgKappaSuspensionKInput R A (s A).cone` とする。
cone の全 Hom 作用を、懸垂の全 Hom 作用と同一視しない。

残る工程：

- cone の入力全 Hom 作用を、同じ cell 分解比較関手へ延長する。
- 同じ選択 ε を持つ商関手の族へ延長し、収縮との整合を証明する。
  元 Hom の自然性だけでは ε 整合は出ない。`ParameterExtension` の必要十分条件を
  使用する。新しい商への置換や収縮の変更で条件を消さない。
- 固定 PerfDGInput の全 Hom に対する SSet 射作用を構成する。
- 豊穣単位・合成と高次比較を証明し、coherentNerveMap を得る。
- 頂点の厳密等号と、元の実商関手の辺との端点固定 VertexIso を照合する。
- 正本 `DGSuspensionCoherentActionInput` を構成し、K-B3 の K-7 c4 へ公開名を報告。

単独の cone 関手、通常射の恒等・合成則、対象別存在だけで
全単体作用 map と edgeIso が供給済みになったとは数えない。

## 検証

独自集約：`ClosureFunctoriality/All.lean`、`SuspensionAction/All.lean`。
両集約のビルド成功、監査は終了コード 0。所有範囲のソース走査と空白検査も通過。
独自監査は全新規葉の全宣言を走査し、許可公理を
`propext`、`Classical.choice`、`Quot.sound` のみに限定する。
`sorryAx` は不許可。共有監査の編集は行わない。

検証コマンド：

```sh
lake build SerrePositivity.InfinityCategories.Derived.ClosureFunctoriality.All SerrePositivity.InfinityCategories.Derived.SuspensionAction.All
lake env lean scripts/audit_derived_closure_functoriality.lean
```
