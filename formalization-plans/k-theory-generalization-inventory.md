# 任意モデル源への一般化（中断）：モジュール棚卸し

この記録は分類・docstring整備と配置提案であり、§396の一般化を再開・完了したものではない。宣言名・型・証明・importは変更せず、ファイルの移動・削除も行わない。

## 対象の確定

§224以降を、stage 4のS3完了時点 `9969643992424d419484ab27069a24b8973b45d7` から、この棚卸し開始時に取得した追加ファイル集合で切り出した。`git log --diff-filter=A` の追加コミット・日時を各行に記録する。対象は `CategoryTheory/` と `HomotopicalAlgebra/` 配下の追跡済み618本。既存ファイルの変更だけは本数に含めない。

|分類|本数|意味|
|---|---:|---|
|A|190|主張・構成が独立して再利用可能。ただし現在のimportまでBから独立するという意味ではない。|
|B|413|任意モデル源の厳密化・選択・小値化に特化した足場。数学的に不要という判定ではない。|
|C|15|一般的な主張と専用APIが混在し、独立した契約を未確定。|

ディレクトリ別：CategoryTheory 45、HomotopyFunctionComplex直下282・Reedy 7、Simplicial 280、Generated 1・Quillen 1・Replacement 2。合計618。

|ディレクトリ|A|B|C|計|
|---|---:|---:|---:|---:|
|CategoryTheory|20|25|0|45|
|Generated|1|0|0|1|
|HomotopyFunctionComplex|11|267|4|282|
|HomotopyFunctionComplex/Reedy|7|0|0|7|
|Quillen|1|0|0|1|
|Replacement|2|0|0|2|
|Simplicial|148|121|11|280|

未追跡 `Simplicial/RelativeFillerComparison.lean` はgit logの追加集合に含めず、付記として保存状態だけ記録する。中断時から型検査未完了であり、今回編集・import・コミットしない。A/B/C本数には含めない。

## 読み方と監査範囲

各モジュールに固定アンカーm0001〜m0618を付ける。「公開名」はコンパイル済み `.ilean` の宣言表から取得した実在名で、Aは主入口、B/Cは代表的な先頭・終端の公開名である。自動生成・private名は入口として選ばない。全公開宣言の網羅表ではない。

「直接import元」はプロジェクトのLeanソース上の逆辺。「宣言参照元」は `.ilean` の参照表にそのモジュールの宣言へのusageがある別モジュール。再公開importだけなら後者には現れない。参照表は今回のビルドで生成済みのプロジェクト成果物が対象で、別チャットの未ビルドWIPや外部利用者までは含まない。使用なしはこの範囲での記録である。

**stage 4の完成部分L・E・Sからは618本すべて利用なし。** [独立監査](stage4-dependency-audit.md)の79入口・663本の閉包に対象618本が含まれないことを照合した。各行のL/E/S欄はこの推移的import閉包による判定。共有Foundationsへの収録とは区別する。

## Aの主要な入口と今後のK理論

以下の各A行で、公開名・日本語の主張・想定用途を一行ずつ記録する。特に対角・realization・DiagonalQuillen、Kanの相対持ち上げとホモトピー拡張、pullback変形と余極限比較、π₀、nerve、bar・余モナド分解が入口となる。S-構成・加法性・局所化・π_*への適用自体をこの棚卸しで証明したわけではない。

|代表的な入口|公開名と主張|
|---|---|
|[DiagonalQuillen](#m0387)|`SerrePositivity.BisimplicialModel.diagonal_map_weakEquivalence` — 各行が弱同値である二重単体写像の対角も弱同値となる。|
|[DiagonalLocalizedEquivalence](#m0385)|`SerrePositivity.BisimplicialModel.localized_diagonal_map` — 各行で局所化可逆な二重単体写像の対角は局所化可逆となる。|
|[KanHomotopyExtension](#m0414)|`SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_homotopy` — anodyne射への制限後のホモトピーから元の両射を結ぶKan値ホモトピーの存在を導く。|
|[KanPullbackDeformation](#m0428)|`SerrePositivity.SimplicialModel.KanPullbackDeformation.exists_retraction` — 強変形レトラクトをKan fibrationに沿って引き戻した実際のレトラクションを構成する。|
|[KanSequentialColimitComparison](#m0436)|`SerrePositivity.SimplicialModel.KanSequentialColimitComparison.actual_localized_isIso` — 逐次図式の局所化可逆な比較は実際の余極限上でも局所化可逆となる。|
|[PiZeroConstant](#m0512)|`SerrePositivity.SimplicialModel.PiZeroConstant.homotopy_eq` — 離散単体的集合を値とするホモトピックな二射は等しい。|
|[NerveHomotopy](#m0012)|`SerrePositivity.NerveHomotopy.homotopy` — 自然変換から圏のnerveの間の実単体的ホモトピーを構成する。|
|[BarConstruction](#m0347)|`SerrePositivity.SimplicialModel.BarConstruction.functor` — 添字と値の宇宙を分けたモデル構造不要のbar関手を構成する。|
|[ComonadSimplicialResolution](#m0077)|`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution.diagram` — 任意の余モナドから通常の単体圏上の単体的分解を構成する。|

## Bの数学的な位置づけ

Dwyer–Kanの自由単体的resolution・単体的局所化は、自由生成した射列、word presentation、resolution圏を理解するための技法上の対応である。[Dwyer–Kan, Simplicial localizations of categories (1980)](https://www.sciencedirect.com/science/article/pii/0022404980900493) を参照。現行コードと同論文の構成の一致や比較同値を主張しない。

整合図式を厳密な図式へ移す方向は [Lurie, HTT §4.2.4](https://arxiv.org/pdf/math/0608040) と関連する。同節、とくに命題4.2.4.4は組合せ的な単体モデル圏などの仮定を持つ。今回の一般化をその定理の形式化・適用済みと読むことはできない。

正規化horn、相対選択空間、比較三角形・四面体は、指定した端・既存の退化・自然性を保持した充填を実際に選ぶための足場である。扱うKan性は**すべてのhorn**に対する持ち上げであり、準圏の内部horn条件ではない。将来の∞圏化で技法の参考にはなるが、そのまま準圏の厳密化定理にはならない。小値化の商も、同値類の普遍性だけから小さい厳密な双関手が得られると主張するものではない。

## モジュール別分類・入口・使用箇所

<a id="m0001"></a>

### m0001 · CategoryTheory.AnchoredChain

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChain.lean](../SerrePositivity/CategoryTheory/AnchoredChain.lean)|
|追加|2026-10-16T11:27:18+09:00 · `05ef2e5dcdf3`|
|主な公開宣言|`SerrePositivity.ArrowFactorization`<br>`SerrePositivity.AnchoredChain.cut_reindex_id`<br>`SerrePositivity.AnchoredChain.cut_reindex_comp`|
|直接import元|[CategoryTheory.AnchoredChainSimplicial](#m0004)<br>[CategoryTheory.ArrowFactorizationCategory](#m0007)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)|
|宣言参照元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[CategoryTheory.AnchoredChainNerve](#m0003)<br>[CategoryTheory.AnchoredChainSimplicial](#m0004)<br>[CategoryTheory.AnchoredChainTransport](#m0005)<br>[CategoryTheory.ArrowContext](#m0006)<br>[CategoryTheory.ArrowFactorizationCategory](#m0007)<br>[CategoryTheory.ArrowFactorizationTransport](#m0008)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Composable chains with fixed external endpoints。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0002"></a>

### m0002 · CategoryTheory.AnchoredChainContraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChainContraction.lean](../SerrePositivity/CategoryTheory/AnchoredChainContraction.lean)|
|追加|2026-10-16T11:44:29+09:00 · `cc1a202bc6f3`|
|主な公開宣言|`SerrePositivity.AnchoredChain.nerveCollapse`<br>`SerrePositivity.AnchoredChain.basePoint_collapse`<br>`SerrePositivity.AnchoredChain.contraction`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A simultaneous simplicial contraction of all anchored chains。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0003"></a>

### m0003 · CategoryTheory.AnchoredChainNerve

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChainNerve.lean](../SerrePositivity/CategoryTheory/AnchoredChainNerve.lean)|
|追加|2026-10-16T11:36:03+09:00 · `a146445e04fe`|
|主な公開宣言|`SerrePositivity.AnchoredChain.cutDiagram`<br>`SerrePositivity.AnchoredChain.fromNerve_isIso`<br>`SerrePositivity.AnchoredChain.nerveIso`|
|直接import元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[CategoryTheory.AnchoredChainTransport](#m0005)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)|
|宣言参照元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[CategoryTheory.AnchoredChainTransport](#m0005)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All anchored chains are the nerve of the factorization category。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0004"></a>

### m0004 · CategoryTheory.AnchoredChainSimplicial

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChainSimplicial.lean](../SerrePositivity/CategoryTheory/AnchoredChainSimplicial.lean)|
|追加|2026-10-16T11:27:18+09:00 · `05ef2e5dcdf3`|
|主な公開宣言|`SerrePositivity.AnchoredChain.simplicial`|
|直接import元|[CategoryTheory.AnchoredChainNerve](#m0003)<br>[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[CategoryTheory.AnchoredChainNerve](#m0003)<br>[CategoryTheory.AnchoredChainTransport](#m0005)<br>[CategoryTheory.ArrowContext](#m0006)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual simplicial set of chains with fixed external endpoints。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0005"></a>

### m0005 · CategoryTheory.AnchoredChainTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChainTransport.lean](../SerrePositivity/CategoryTheory/AnchoredChainTransport.lean)|
|追加|2026-10-16T12:13:35+09:00 · `f34b16b8364a`|
|主な公開宣言|`SerrePositivity.AnchoredChain.mapFunctor`<br>`SerrePositivity.AnchoredChain.transport_diagram`<br>`SerrePositivity.AnchoredChain.mapFunctor_pre_post`|
|直接import元|[CategoryTheory.ArrowContext](#m0006)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)|
|宣言参照元|[CategoryTheory.ArrowContext](#m0006)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict external transport of the entire simplicial chain parameter。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0006"></a>

### m0006 · CategoryTheory.ArrowContext

|項目|記録|
|---|---|
|分類|B|
|ソース|[ArrowContext.lean](../SerrePositivity/CategoryTheory/ArrowContext.lean)|
|追加|2026-10-16T15:09:35+09:00 · `673dd59a1084`|
|主な公開宣言|`SerrePositivity.ArrowContext.homs`<br>`SerrePositivity.ArrowContext.parameters_diagram`<br>`SerrePositivity.ArrowContext.parameters_cut`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One category of changing central arrows and its actual factorization parameters。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0007"></a>

### m0007 · CategoryTheory.ArrowFactorizationCategory

|項目|記録|
|---|---|
|分類|A|
|ソース|[ArrowFactorizationCategory.lean](../SerrePositivity/CategoryTheory/ArrowFactorizationCategory.lean)|
|追加|2026-10-16T11:36:03+09:00 · `a146445e04fe`|
|主な公開宣言|`SerrePositivity.ArrowFactorization.target_isTerminal`|
|直接import元|[CategoryTheory.AnchoredChainNerve](#m0003)<br>[CategoryTheory.ArrowFactorizationTransport](#m0008)|
|宣言参照元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[CategoryTheory.AnchoredChainNerve](#m0003)<br>[CategoryTheory.AnchoredChainTransport](#m0005)<br>[CategoryTheory.ArrowFactorizationTransport](#m0008)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ArrowFactorization.target_isTerminal` — 固定した射の因子分解圏で終域側の自明な因子分解が終対象となる。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0008"></a>

### m0008 · CategoryTheory.ArrowFactorizationTransport

|項目|記録|
|---|---|
|分類|A|
|ソース|[ArrowFactorizationTransport.lean](../SerrePositivity/CategoryTheory/ArrowFactorizationTransport.lean)|
|追加|2026-10-16T12:13:35+09:00 · `f34b16b8364a`|
|主な公開宣言|`SerrePositivity.ArrowFactorization.transport_comp`|
|直接import元|[CategoryTheory.AnchoredChainTransport](#m0005)|
|宣言参照元|[CategoryTheory.AnchoredChainTransport](#m0005)<br>[CategoryTheory.ArrowContext](#m0006)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ArrowFactorization.transport_comp` — 因子分解圏の外側の射に沿う移送が合成と整合する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0009"></a>

### m0009 · CategoryTheory.ElementsNaturalPrecomp

|項目|記録|
|---|---|
|分類|A|
|ソース|[ElementsNaturalPrecomp.lean](../SerrePositivity/CategoryTheory/ElementsNaturalPrecomp.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.ElementsNaturalPrecomp.comparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ElementsNaturalPrecomp.comparison` — 自然変換に沿う圏の要素の比較関手を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0010"></a>

### m0010 · CategoryTheory.LabelledChain

|項目|記録|
|---|---|
|分類|B|
|ソース|[LabelledChain.lean](../SerrePositivity/CategoryTheory/LabelledChain.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.LabelledChain.eqToHom_hom`<br>`SerrePositivity.LabelledChain.lift_heq`<br>`SerrePositivity.LabelledChain.ext_of_first`|
|直接import元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveFunctor](#m0565)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|宣言参照元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveFunctor](#m0565)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Lifting a whole chain from its original first label。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0011"></a>

### m0011 · CategoryTheory.Limits.SequentialExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[SequentialExtension.lean](../SerrePositivity/CategoryTheory/Limits/SequentialExtension.lean)|
|追加|2026-10-16T10:49:09+09:00 · `fe7468c4b2dc`|
|主な公開宣言|`SerrePositivity.SequentialExtension.descend`|
|直接import元|[HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension](#m0518)<br>[HomotopicalAlgebra.Simplicial.SkeletalCellGluing](#m0569)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension](#m0518)<br>[HomotopicalAlgebra.Simplicial.SkeletalCellGluing](#m0569)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SequentialExtension.descend` — 整合的な逐次延長族から余極限上の射を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0012"></a>

### m0012 · CategoryTheory.NerveHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveHomotopy.lean](../SerrePositivity/CategoryTheory/NerveHomotopy.lean)|
|追加|2026-10-16T11:44:29+09:00 · `cc1a202bc6f3`|
|主な公開宣言|`SerrePositivity.NerveHomotopy.homotopy`|
|直接import元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[HomotopicalAlgebra.Simplicial.NerveInitialImage](#m0474)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)|
|宣言参照元|[CategoryTheory.AnchoredChainContraction](#m0002)<br>[HomotopicalAlgebra.Simplicial.NerveInitialImage](#m0474)<br>[HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators](#m0523)<br>[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)<br>[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveHomotopy.homotopy` — 自然変換から圏のnerveの間の実単体的ホモトピーを構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0013"></a>

### m0013 · CategoryTheory.NerveHomotopyUniverse

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveHomotopyUniverse.lean](../SerrePositivity/CategoryTheory/NerveHomotopyUniverse.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.NerveHomotopyUniverse.homotopy`<br>`SerrePositivity.NerveHomotopyUniverse.at_zero`|
|直接import元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|宣言参照元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveHomotopyUniverse.homotopy` — 対象と射の宇宙を分けたまま自然変換からnerveのホモトピーを構成する。|
|入口の主張|`SerrePositivity.NerveHomotopyUniverse.at_zero` — 独立した宇宙で構成したnerveのホモトピーの始点が指定した関手に一致する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0014"></a>

### m0014 · CategoryTheory.NerveSimplexEndpoint

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveSimplexEndpoint.lean](../SerrePositivity/CategoryTheory/NerveSimplexEndpoint.lean)|
|追加|2026-10-16T13:43:22+09:00 · `1de52e9af25a`|
|主な公開宣言|`SerrePositivity.NerveSimplexEndpoint.functor`|
|直接import元|[CategoryTheory.NerveSimplexStart](#m0016)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentFamily](#m0466)|
|宣言参照元|[CategoryTheory.NerveSimplexStart](#m0016)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentExtension](#m0465)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentFamily](#m0466)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentReindex](#m0467)<br>[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveSimplexEndpoint.functor` — nerveの単体圏から終端頂点を評価する関手を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0015"></a>

### m0015 · CategoryTheory.NerveSimplexFirstFunctor

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveSimplexFirstFunctor.lean](../SerrePositivity/CategoryTheory/NerveSimplexFirstFunctor.lean)|
|追加|2026-10-16T23:36:02+09:00 · `59633177dfe3`|
|主な公開宣言|`SerrePositivity.NerveSimplexFirstFunctor.augmentation_eq`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveSimplexFirstFunctor.augmentation_eq` — 先頭単体を取る関手が元のnerve augmentationを回収する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0016"></a>

### m0016 · CategoryTheory.NerveSimplexStart

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveSimplexStart.lean](../SerrePositivity/CategoryTheory/NerveSimplexStart.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.NerveSimplexStart.functor`|
|直接import元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)|
|宣言参照元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveSimplexStart.functor` — nerveの単体圏から先頭頂点を反変に評価する関手を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0017"></a>

### m0017 · CategoryTheory.NerveVertices

|項目|記録|
|---|---|
|分類|A|
|ソース|[NerveVertices.lean](../SerrePositivity/CategoryTheory/NerveVertices.lean)|
|追加|2026-10-16T11:58:45+09:00 · `bfdca7e488b2`|
|主な公開宣言|`SerrePositivity.NerveVertices.inclusion`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.NerveVertices.inclusion` — 圏のnerveにその頂点部分単体集合を含める射を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0018"></a>

### m0018 · CategoryTheory.Presentation.AmbientWordAugmentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWordAugmentation.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWordAugmentation.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.AmbientWords.augmentationRealization`<br>`SerrePositivity.AmbientWords.augmentation_source`<br>`SerrePositivity.AmbientWords.augmentation_word`|
|直接import元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual augmentation forgets all ambient word actions。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0019"></a>

### m0019 · CategoryTheory.Presentation.AmbientWordComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWordComparison.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWordComparison.lean)|
|追加|2026-10-17T08:32:16+09:00 · `29fd7a58a5a4`|
|主な公開宣言|`SerrePositivity.AmbientWords.toRetract_decode`<br>`SerrePositivity.AmbientWords.toRetract_decodeHom`<br>`SerrePositivity.AmbientWords.ambientHomEquiv`|
|直接import元|[CategoryTheory.Presentation.AmbientWordMap](#m0022)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The ambient word embedding has an explicit inverse on ambient Hom sets。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0020"></a>

### m0020 · CategoryTheory.Presentation.AmbientWordFunctoriality

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWordFunctoriality.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWordFunctoriality.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.AmbientWords.map_id`<br>`SerrePositivity.AmbientWords.map_augmentation`<br>`SerrePositivity.AmbientWords.toRetract_augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict functoriality and naturality of the actual ambient-word augmentation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0021"></a>

### m0021 · CategoryTheory.Presentation.AmbientWordKaroubi

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWordKaroubi.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWordKaroubi.lean)|
|追加|2026-10-17T08:32:16+09:00 · `29fd7a58a5a4`|
|主な公開宣言|`SerrePositivity.AmbientWords.loop`<br>`SerrePositivity.AmbientWords.decodeRealization`<br>`SerrePositivity.AmbientWords.decode`|
|直接import元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.AmbientWordMap](#m0022)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Decode formal retract vertices as actual idempotents of the ambient word presentation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0022"></a>

### m0022 · CategoryTheory.Presentation.AmbientWordMap

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWordMap.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWordMap.lean)|
|追加|2026-10-17T08:32:16+09:00 · `29fd7a58a5a4`|
|主な公開宣言|`SerrePositivity.AmbientWords.mapRealization`<br>`SerrePositivity.AmbientWords.map_loop`<br>`SerrePositivity.AmbientWords.map_toRetract`|
|直接import元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The ambient comparison commutes with source and word parameter maps。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0023"></a>

### m0023 · CategoryTheory.Presentation.AmbientWords

|項目|記録|
|---|---|
|分類|B|
|ソース|[AmbientWords.lean](../SerrePositivity/CategoryTheory/Presentation/AmbientWords.lean)|
|追加|2026-10-17T08:32:16+09:00 · `29fd7a58a5a4`|
|主な公開宣言|`SerrePositivity.AmbientWords.Vertex`<br>`SerrePositivity.AmbientWords.Realization.functor_word`<br>`SerrePositivity.AmbientWords.functor_ext_generators`|
|直接import元|[CategoryTheory.Presentation.AmbientWordAugmentation](#m0018)<br>[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[CategoryTheory.Presentation.WeightedPathRealization](#m0032)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordAugmentation](#m0018)<br>[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[CategoryTheory.Presentation.AmbientWordMap](#m0022)<br>[CategoryTheory.Presentation.WeightedPathRealization](#m0032)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Source categories with independent monoid actions adjoined at each object。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0024"></a>

### m0024 · CategoryTheory.Presentation.RetractWordAugmentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordAugmentation.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordAugmentation.lean)|
|追加|2026-10-17T07:58:03+09:00 · `242f0f56cea2`|
|主な公開宣言|`SerrePositivity.RetractWords.augmentation_source`<br>`SerrePositivity.RetractWords.map_augmentation`<br>`SerrePositivity.RetractWords.source_map`|
|直接import元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Naturality of the actual augmentation in source and word parameters。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0025"></a>

### m0025 · CategoryTheory.Presentation.RetractWordExt

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordExt.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordExt.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.RetractWords.functor_ext_generators`|
|直接import元|[CategoryTheory.Presentation.RetractWordAugmentation](#m0024)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)|
|宣言参照元|[CategoryTheory.Presentation.RetractWordAugmentation](#m0024)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Extensionality on the actual generating arrows of the retract-word quotient。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0026"></a>

### m0026 · CategoryTheory.Presentation.RetractWordIdentities

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordIdentities.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordIdentities.lean)|
|追加|2026-10-17T08:25:11+09:00 · `7c5e24aa8ffe`|
|主な公開宣言|`SerrePositivity.RetractWords.quotient_word_one`<br>`SerrePositivity.RetractWords.quotient_word_zero`<br>`SerrePositivity.RetractWords.quotient_split`|
|直接import元|[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The defining retract relations as equalities of actual quotient arrows。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0027"></a>

### m0027 · CategoryTheory.Presentation.RetractWordMap

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordMap.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordMap.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.RetractWords.mapRealization`<br>`SerrePositivity.RetractWords.map_comp_raw`<br>`SerrePositivity.RetractWords.map_comp`|
|直接import元|[CategoryTheory.Presentation.AmbientWordMap](#m0022)<br>[CategoryTheory.Presentation.RetractWordAugmentation](#m0024)<br>[CategoryTheory.Presentation.RetractWordPullback](#m0028)<br>[HomotopicalAlgebra.Simplicial.WordPresentationDiagram](#m0610)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordMap](#m0022)<br>[CategoryTheory.Presentation.RetractWordAugmentation](#m0024)<br>[CategoryTheory.Presentation.RetractWordPullback](#m0028)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)<br>[HomotopicalAlgebra.Simplicial.WordPresentationCat](#m0609)<br>[HomotopicalAlgebra.Simplicial.WordPresentationDiagram](#m0610)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSourceMap](#m0614)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Functoriality of the retract-word presentation in source and word parameters。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0028"></a>

### m0028 · CategoryTheory.Presentation.RetractWordPullback

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordPullback.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordPullback.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.RetractWords.Realization.pullback`<br>`SerrePositivity.RetractWords.Realization.pullback_functor`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Pull back actual realizations along source functors and word homomorphisms。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0029"></a>

### m0029 · CategoryTheory.Presentation.RetractWordRealization

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWordRealization.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWordRealization.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.RetractWords.Realization`<br>`SerrePositivity.RetractWords.Realization.functor_projection`<br>`SerrePositivity.RetractWords.Realization.source_functor`|
|直接import元|[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[CategoryTheory.Presentation.RetractWordMap](#m0027)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[CategoryTheory.Presentation.RetractWordMap](#m0027)<br>[CategoryTheory.Presentation.RetractWordPullback](#m0028)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluate the retract-word presentation in any category。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0030"></a>

### m0030 · CategoryTheory.Presentation.RetractWords

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractWords.lean](../SerrePositivity/CategoryTheory/Presentation/RetractWords.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.RetractWords.Vertex`<br>`SerrePositivity.RetractWords.smallAugmentation`<br>`SerrePositivity.RetractWords.source_augmentation`|
|直接import元|[CategoryTheory.Presentation.RetractWordExt](#m0025)<br>[CategoryTheory.Presentation.RetractWordIdentities](#m0026)<br>[CategoryTheory.Presentation.RetractWordRealization](#m0029)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[CategoryTheory.Presentation.AmbientWordFunctoriality](#m0020)<br>[CategoryTheory.Presentation.AmbientWordKaroubi](#m0021)<br>[CategoryTheory.Presentation.RetractWordAugmentation](#m0024)<br>[CategoryTheory.Presentation.RetractWordExt](#m0025)<br>[CategoryTheory.Presentation.RetractWordIdentities](#m0026)<br>[CategoryTheory.Presentation.RetractWordMap](#m0027)<br>[CategoryTheory.Presentation.RetractWordPullback](#m0028)<br>[CategoryTheory.Presentation.RetractWordRealization](#m0029)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)<br>[HomotopicalAlgebra.Simplicial.WordPresentationCat](#m0609)<br>[HomotopicalAlgebra.Simplicial.WordPresentationDiagram](#m0610)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSourceMap](#m0614)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A category presented by source arrows, contraction words, and split retracts。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0031"></a>

### m0031 · CategoryTheory.Presentation.WeightedPathParameterMap

|項目|記録|
|---|---|
|分類|B|
|ソース|[WeightedPathParameterMap.lean](../SerrePositivity/CategoryTheory/Presentation/WeightedPathParameterMap.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.QuiverWeightedPaths.augmentation_eval`<br>`SerrePositivity.QuiverWeightedPaths.parameter_source`<br>`SerrePositivity.QuiverWeightedPaths.map_eval`|
|直接import元|[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Normal forms preserve the actual word-parameter maps and augmentation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0032"></a>

### m0032 · CategoryTheory.Presentation.WeightedPathRealization

|項目|記録|
|---|---|
|分類|B|
|ソース|[WeightedPathRealization.lean](../SerrePositivity/CategoryTheory/Presentation/WeightedPathRealization.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.QuiverWeightedPaths.target`<br>`SerrePositivity.QuiverWeightedPaths.decode_encode`<br>`SerrePositivity.QuiverWeightedPaths.normalFormEquiv`|
|直接import元|[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)|
|宣言参照元|[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation of weighted paths in the actual ambient word quotient。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0033"></a>

### m0033 · CategoryTheory.Quiver.PathFunctorExt

|項目|記録|
|---|---|
|分類|A|
|ソース|[PathFunctorExt.lean](../SerrePositivity/CategoryTheory/Quiver/PathFunctorExt.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.QuiverPaths.functor_ext_edges`|
|直接import元|[CategoryTheory.Presentation.AmbientWords](#m0023)<br>[CategoryTheory.Presentation.RetractWordExt](#m0025)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWords](#m0023)<br>[CategoryTheory.Presentation.RetractWordExt](#m0025)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.QuiverPaths.functor_ext_edges` — 自由な道の圏からの関手は対象と生成辺上の値で決まる。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0034"></a>

### m0034 · CategoryTheory.Quiver.PathIntersections

|項目|記録|
|---|---|
|分類|A|
|ソース|[PathIntersections.lean](../SerrePositivity/CategoryTheory/Quiver/PathIntersections.lean)|
|追加|2026-10-17T06:12:59+09:00 · `c46a1300275c`|
|主な公開宣言|`SerrePositivity.QuiverPaths.mapPath_intersection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies](#m0093)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies](#m0093)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.QuiverPaths.mapPath_intersection` — 対象を固定する辺の写像の交わりが道への写像でも保たれる。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0035"></a>

### m0035 · CategoryTheory.Quiver.PathNatTrans

|項目|記録|
|---|---|
|分類|A|
|ソース|[PathNatTrans.lean](../SerrePositivity/CategoryTheory/Quiver/PathNatTrans.lean)|
|追加|2026-10-17T07:45:39+09:00 · `3ff83b21eecb`|
|主な公開宣言|`SerrePositivity.QuiverPaths.natTransOfEdges`|
|直接import元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)|
|宣言参照元|[CategoryTheory.Presentation.AmbientWordComparison](#m0019)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.QuiverPaths.natTransOfEdges` — 生成辺上の自然性から道の圏上の自然変換を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0036"></a>

### m0036 · CategoryTheory.Quiver.PathObjectTransport

|項目|記録|
|---|---|
|分類|A|
|ソース|[PathObjectTransport.lean](../SerrePositivity/CategoryTheory/Quiver/PathObjectTransport.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.QuiverPaths.counit_copy_singleton`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.QuiverPaths.counit_copy_singleton` — 対象の移送後の単一辺の道を余単位で評価すると元の辺の移送に一致する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0037"></a>

### m0037 · CategoryTheory.Quiver.WeightedPathMaps

|項目|記録|
|---|---|
|分類|B|
|ソース|[WeightedPathMaps.lean](../SerrePositivity/CategoryTheory/Quiver/WeightedPathMaps.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.QuiverWeightedPaths.mapWeights`<br>`SerrePositivity.QuiverWeightedPaths.mapWeights_fill`<br>`SerrePositivity.QuiverWeightedPaths.mapWeights_const`|
|直接import元|[CategoryTheory.Presentation.WeightedPathRealization](#m0032)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)|
|宣言参照元|[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Arbitrary weight substitutions and the underlying unweighted path。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0038"></a>

### m0038 · CategoryTheory.Quiver.WeightedPaths

|項目|記録|
|---|---|
|分類|B|
|ソース|[WeightedPaths.lean](../SerrePositivity/CategoryTheory/Quiver/WeightedPaths.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.QuiverWeightedPaths.Path`<br>`SerrePositivity.QuiverWeightedPaths.generators`<br>`SerrePositivity.QuiverWeightedPaths.sourceFunctor`|
|直接import元|[CategoryTheory.Quiver.WeightedPathMaps](#m0037)|
|宣言参照元|[CategoryTheory.Presentation.WeightedPathParameterMap](#m0031)<br>[CategoryTheory.Presentation.WeightedPathRealization](#m0032)<br>[CategoryTheory.Quiver.WeightedPathMaps](#m0037)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Paths with independent monoid weights at every vertex。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0039"></a>

### m0039 · CategoryTheory.Simplex.Naturality

|項目|記録|
|---|---|
|分類|A|
|ソース|[Naturality.lean](../SerrePositivity/CategoryTheory/Simplex/Naturality.lean)|
|追加|2026-10-17T06:46:13+09:00 · `b5aca038f600`|
|主な公開宣言|`SerrePositivity.SimplexNaturality.ofFacesDegeneracies`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval](#m0397)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval](#m0397)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexNaturality.ofFacesDegeneracies` — 面と退化に関する可換性から単体的な自然変換を組み立てる。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0040"></a>

### m0040 · CategoryTheory.Simplex.Prefix

|項目|記録|
|---|---|
|分類|A|
|ソース|[Prefix.lean](../SerrePositivity/CategoryTheory/Simplex/Prefix.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.SimplexPrefix.functor`|
|直接import元|[CategoryTheory.Simplex.PrefixInterval](#m0041)|
|宣言参照元|[CategoryTheory.Simplex.PrefixInterval](#m0041)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval](#m0397)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexPrefix.functor` — 単体に先頭頂点を一つ追加する関手を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0041"></a>

### m0041 · CategoryTheory.Simplex.PrefixInterval

|項目|記録|
|---|---|
|分類|A|
|ソース|[PrefixInterval.lean](../SerrePositivity/CategoryTheory/Simplex/PrefixInterval.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.SimplexPrefix.cut_zero_factor`|
|直接import元|[HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval](#m0397)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval](#m0397)<br>[HomotopicalAlgebra.Simplicial.OppositeHomotopy](#m0506)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexPrefix.cut_zero_factor` — 区間の始点における先頭頂点の移動が指定した零頂点の写像を経由する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0042"></a>

### m0042 · CategoryTheory.Simplex.PresentationDegeneracies

|項目|記録|
|---|---|
|分類|A|
|ソース|[PresentationDegeneracies.lean](../SerrePositivity/CategoryTheory/Simplex/PresentationDegeneracies.lean)|
|追加|2026-10-17T05:19:20+09:00 · `c7eed07998d7`|
|主な公開宣言|`SerrePositivity.SimplexPresentation.map_injective_on_degeneracies`|
|直接import元|[CategoryTheory.Simplex.PresentationFaces](#m0044)|
|宣言参照元|[CategoryTheory.Simplex.PresentationEquivalence](#m0043)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexPresentation.map_injective_on_degeneracies` — 表示された単体圏から通常の単体圏への写像は退化の標準形を区別する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0043"></a>

### m0043 · CategoryTheory.Simplex.PresentationEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[PresentationEquivalence.lean](../SerrePositivity/CategoryTheory/Simplex/PresentationEquivalence.lean)|
|追加|2026-10-17T05:19:20+09:00 · `c7eed07998d7`|
|主な公開宣言|`SerrePositivity.SimplexPresentation.equivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution](#m0077)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution](#m0077)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexPresentation.equivalence` — 面と退化の関係式による表示圏と通常の単体圏の同値を構成する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0044"></a>

### m0044 · CategoryTheory.Simplex.PresentationFaces

|項目|記録|
|---|---|
|分類|A|
|ソース|[PresentationFaces.lean](../SerrePositivity/CategoryTheory/Simplex/PresentationFaces.lean)|
|追加|2026-10-17T05:19:20+09:00 · `c7eed07998d7`|
|主な公開宣言|`SerrePositivity.SimplexPresentation.map_injective_on_faces`|
|直接import元|[CategoryTheory.Simplex.PresentationEquivalence](#m0043)|
|宣言参照元|[CategoryTheory.Simplex.PresentationEquivalence](#m0043)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplexPresentation.map_injective_on_faces` — 表示された単体圏から通常の単体圏への写像は面の標準形を区別する。|
|今後の用途|今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。|

<a id="m0045"></a>

### m0045 · CategoryTheory.SimplexChainParameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[SimplexChainParameter.lean](../SerrePositivity/CategoryTheory/SimplexChainParameter.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.SimplexChainParameter.prefix_comp`<br>`SerrePositivity.SimplexChainParameter.parameter_zero`<br>`SerrePositivity.SimplexChainParameter.reindex`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation](#m0563)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|宣言参照元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation](#m0563)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual first-vertex parameter of a chain of simplex operators。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0046"></a>

### m0046 · HomotopicalAlgebra.Generated.FunctorClosure

|項目|記録|
|---|---|
|分類|A|
|ソース|[FunctorClosure.lean](../SerrePositivity/HomotopicalAlgebra/Generated/FunctorClosure.lean)|
|追加|2026-10-16T19:28:07+09:00 · `8fd5e26041a7`|
|主な公開宣言|`SerrePositivity.ModelGeneration.generatedLeft_map`|
|直接import元|[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne](#m0588)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne](#m0588)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ModelGeneration.generatedLeft_map` — 余極限を保つ関手が生成射上で左クラスを保てば生成された左クラス全体を保つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0047"></a>

### m0047 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationChoices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationChoices.lean)|
|追加|2026-10-16T12:51:18+09:00 · `515511d5cd33`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationChoices.valueFillers`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationChoices.simplex`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationChoices.simplex_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One space of all global comparison systems with the prescribed factorization points。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0048"></a>

### m0048 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationCoherentSquare.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationCoherentSquare.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationCoherentSquare.Context`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationCoherentSquare.simplex`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationCoherentSquare.simplex_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallFamilies](#m0058)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One external coherent square retaining the entire old all-factorization parameter。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0049"></a>

### m0049 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationComparison.lean)|
|追加|2026-10-16T11:58:45+09:00 · `bfdca7e488b2`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationComparison.choiceSpace`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationComparison.simplex_fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationComparison.action_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One comparison family on all factorization chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0050"></a>

### m0050 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationMixed.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationMixed.lean)|
|追加|2026-10-16T12:32:15+09:00 · `561db7ce10aa`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixed.choiceSpace`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixed.simplex_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixed.simplex_fixed_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One mixed square over all factorization chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0051"></a>

### m0051 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationMixedContext.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationMixedContext.lean)|
|追加|2026-10-16T13:34:33+09:00 · `1972260f2353`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedContext.context`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedContext.simplex`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedContext.simplex_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The already selected global mixed square in the strict context diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0052"></a>

### m0052 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationMixedTransport.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationMixedTransport.lean)|
|追加|2026-10-16T12:32:15+09:00 · `561db7ce10aa`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedTransport.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedTransport.mapAC_tail`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixedTransport.mapBD_tail`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict transport of the global source comparison through target composition。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0053"></a>

### m0053 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationPost.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationPost.lean)|
|追加|2026-10-16T12:13:35+09:00 · `f34b16b8364a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPost.choiceSpace`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPost.simplex`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPost.simplex_fixed_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One postcomposition homotopy on all factorization chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0054"></a>

### m0054 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationPostPoints.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationPostPoints.lean)|
|追加|2026-10-16T13:06:48+09:00 · `25a7578eda56`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints.choiceCast_postMap`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostPoints.point_post`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Exact external postcomposition of the prescribed factorization points。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0055"></a>

### m0055 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationPostRelative.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationPostRelative.lean)|
|追加|2026-10-16T13:06:48+09:00 · `25a7578eda56`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostRelative.vertexMap`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostRelative.oldComparison`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPostRelative.oldComparison_fixed_endpoints`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Postcomposition comparison relative to every prescribed factorization point。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0056"></a>

### m0056 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationPre.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationPre.lean)|
|追加|2026-10-16T12:22:50+09:00 · `b2a1d411792b`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPre.choiceSpace`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPre.simplex_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationPre.simplex_fixed_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Source precomposition of the global factorization comparison。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0057"></a>

### m0057 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationSmallAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationSmallAction.lean)|
|追加|2026-10-16T18:12:55+09:00 · `6bfedb29b930`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallAction.centers`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallAction.lift_factor`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallAction.action_factor`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The old whole factorization square acts on small Hom spaces throughout external contexts。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0058"></a>

### m0058 · HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[AllFactorizationSmallFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AllFactorizationSmallFamilies.lean)|
|追加|2026-10-16T18:12:55+09:00 · `6bfedb29b930`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallFamilies.smallParameter`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallFamilies.point_recover`<br>`SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallFamilies.original_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Original-universe whole finite families of the old all-factorization square。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0059"></a>

### m0059 · HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredPostComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/AnchoredPostComparison.lean)|
|追加|2026-10-16T11:27:18+09:00 · `05ef2e5dcdf3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.AnchoredPostComparison.factorTriangle`<br>`SerrePositivity.HomotopyFunctionComplex.AnchoredPostComparison.fromDiagram_triangle`<br>`SerrePositivity.HomotopyFunctionComplex.AnchoredPostComparison.ofDiagram_triangle`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual ordinal reindexing of composition chains and their comparisons。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0060"></a>

### m0060 · HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[BalancedResolutionComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/BalancedResolutionComparison.lean)|
|追加|2026-10-16T20:06:05+09:00 · `51e5ba852896`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.BalancedResolutionComparison.rawRight`<br>`SerrePositivity.HomotopyFunctionComplex.BalancedResolutionComparison.rightPiZeroEquiv`<br>`SerrePositivity.HomotopyFunctionComplex.BalancedResolutionComparison.localizedIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A natural small Kan span between the left and right framed double Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0061"></a>

### m0061 · HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping

|項目|記録|
|---|---|
|分類|B|
|ソース|[BiresolutionRawMapping.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/BiresolutionRawMapping.lean)|
|追加|2026-10-16T20:06:05+09:00 · `51e5ba852896`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.BiresolutionRawMapping.rawUncurried`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRawMapping.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRawMapping.comparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison](#m0060)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual double Hom before either Kan comparison。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0062"></a>

### m0062 · HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[BiresolutionRightAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/BiresolutionRightAction.lean)|
|追加|2026-10-16T20:06:05+09:00 · `51e5ba852896`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightAction.Centers`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightAction.action_source_operator`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightAction.action_center`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual opposite-model lift choices act on the right rows of the double Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0063"></a>

### m0063 · HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping

|項目|記録|
|---|---|
|分類|B|
|ソース|[BiresolutionRightMapping.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/BiresolutionRightMapping.lean)|
|追加|2026-10-16T20:06:05+09:00 · `51e5ba852896`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightMapping.sourcePoints`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightMapping.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.BiresolutionRightMapping.comparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison](#m0060)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison](#m0060)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The right-framed double Hom, using the opposite model's actual lift machinery。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0064"></a>

### m0064 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftBaseChange.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftBaseChange.lean)|
|追加|2026-10-16T10:06:21+09:00 · `dbc9096b489f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange.strict`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange.tuples`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftBaseChange.interpolation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual base change of coherent lift tuples and their interpolation。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0065"></a>

### m0065 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftEdges.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftEdges.lean)|
|追加|2026-10-16T09:54:18+09:00 · `0c8eb6c83508`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.postLeftPoint`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.preEdge_at_zero`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.preEdge_at_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Selected relative composition edges with exact endpoints。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0066"></a>

### m0066 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftFaces.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftFaces.lean)|
|追加|2026-10-16T09:42:54+09:00 · `1ff62113d16f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.post_fill_faces`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.pre_fill_faces`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Higher comparison fillers from prescribed compatible composition faces。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0067"></a>

### m0067 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftMixedComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftMixedComparison.lean)|
|追加|2026-10-16T10:26:43+09:00 · `270ce23f6d34`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.pointA`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.triangle_fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.triangle_action_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Mixed comparison square with its selected four edges retained。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0068"></a>

### m0068 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftMixedFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftMixedFamilies.lean)|
|追加|2026-10-16T10:26:43+09:00 · `270ce23f6d34`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.castMap`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.tuple_interchange`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftMixedComparison.final_interchange`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The four families in mixed source/target comparison。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0069"></a>

### m0069 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftPostComposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftPostComposition.lean)|
|追加|2026-10-16T10:06:21+09:00 · `dbc9096b489f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPostComposition.castMap`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPostComposition.triangle_fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPostComposition.triangle_action_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The prescribed composition triangle for two postcomposition comparisons。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0070"></a>

### m0070 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftPreComposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftPreComposition.lean)|
|追加|2026-10-16T10:14:03+09:00 · `a58392045199`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPreComposition.castMap`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPreComposition.triangle_fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftPreComposition.triangle_action_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The selected comparison triangle for two actual source frame maps。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0071"></a>

### m0071 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftRelative.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftRelative.lean)|
|追加|2026-10-16T09:33:29+09:00 · `dfe2314dbf6e`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.vertices`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.preChoiceSpace_extension`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative.pre_relative_homotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative comparisons of whole coherent lift families。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0072"></a>

### m0072 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftTuples.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftTuples.lean)|
|追加|2026-10-16T09:10:54+09:00 · `eaa95550cd85`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftTuples.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftTuples.tripleCompositeAction_face`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftTuples.tripleCompositeAction_last_vertex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simultaneous higher comparisons between strict lift choices。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0073"></a>

### m0073 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftUnitComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftUnitComparison.lean)|
|追加|2026-10-16T10:41:12+09:00 · `a6a9a53c32f4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.postComparisonMap`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.triangle_fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.triangle_action_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Selected unit comparisons against actual standard degeneracies。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0074"></a>

### m0074 · HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[CoherentLiftUnitFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CoherentLiftUnitFamilies.lean)|
|追加|2026-10-16T10:41:12+09:00 · `a6a9a53c32f4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.postCast`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.post_boundary_unit`<br>`SerrePositivity.HomotopyFunctionComplex.CoherentLiftUnitComparison.pre_boundary_unit`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual unit comparison families after their base transports。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0075"></a>

### m0075 · HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionOperators

|項目|記録|
|---|---|
|分類|A|
|ソース|[ComonadResolutionOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ComonadResolutionOperators.lean)|
|追加|2026-10-17T05:10:38+09:00 · `991011af7348`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators.augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation](#m0076)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation](#m0076)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution](#m0077)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces](#m0094)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators.augmentation` — 任意の余モナドの反復冪に元の対象へのaugmentationを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0076"></a>

### m0076 · HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionPresentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[ComonadResolutionPresentation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ComonadResolutionPresentation.lean)|
|追加|2026-10-17T05:10:38+09:00 · `991011af7348`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ComonadResolutionPresentation.augmentationNatTrans`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution](#m0077)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation](#m0100)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution](#m0077)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation](#m0100)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.ComonadResolutionPresentation.augmentationNatTrans` — 余モナドの面と退化の関係式を用いて表示単体圏上のaugmentation自然変換を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0077"></a>

### m0077 · HomotopicalAlgebra.HomotopyFunctionComplex.ComonadSimplicialResolution

|項目|記録|
|---|---|
|分類|A|
|ソース|[ComonadSimplicialResolution.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ComonadSimplicialResolution.lean)|
|追加|2026-10-17T05:19:20+09:00 · `c7eed07998d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution.diagram`<br>`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution.augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution](#m0101)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution](#m0101)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution.diagram` — 任意の余モナドから通常の単体圏上の単体的分解を構成する。|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.ComonadSimplicialResolution.augmentation` — 余モナドの単体的分解から元の対象へのaugmentation自然変換を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0078"></a>

### m0078 · HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialMapFamily

|項目|記録|
|---|---|
|分類|A|
|ソース|[CosimplicialMapFamily.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/CosimplicialMapFamily.lean)|
|追加|2026-10-16T20:21:09+09:00 · `59d542e89f0d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.CosimplicialMapFamily.ofDoubleHom_reindex`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHom](#m0118)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHom](#m0118)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery](#m0119)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport](#m0120)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.CosimplicialMapFamily.ofDoubleHom_reindex` — 二重Homから得た余単体写像族が単体パラメータの制限と整合する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0079"></a>

### m0079 · HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalFrame

|項目|記録|
|---|---|
|分類|C|
|ソース|[DiagonalFrame.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalFrame.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.obj`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionAugmentation_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalFrame.resolutionObj_homotopicallyConstant`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition](#m0080)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows](#m0082)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.Simplicial.DiagonalAdjunction](#m0380)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialMapFamily](#m0078)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition](#m0080)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison](#m0081)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction](#m0105)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery](#m0119)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.Simplicial.DiagonalAdjunction](#m0380)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|対角frameの補題は一般化候補だが、resolutionの選択APIとの結合が残る。|
|現状の構成|Diagonals of double cosimplicial objects。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0080"></a>

### m0080 · HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition

|項目|記録|
|---|---|
|分類|C|
|ソース|[DiagonalHomComposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalHomComposition.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DiagonalHom.source`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalHom.pairing_middle_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalHom.pairing_source_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialMapFamily](#m0078)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction](#m0105)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction](#m0105)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery](#m0119)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|対角Homの合成は一般化候補だが、選択したresolution間の合成を入力する。|
|現状の構成|Actual composition from double resolutions into diagonal Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0081"></a>

### m0081 · HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[DiagonalMappingComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalMappingComparison.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.iso`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.comparison_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Identifying diagonal row comparisons with actual Hom precomposition。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0082"></a>

### m0082 · HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingRows

|項目|記録|
|---|---|
|分類|C|
|ソース|[DiagonalMappingRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalMappingRows.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows.obj`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows.row_kanComplex`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingRows.comparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison](#m0081)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows](#m0304)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingComparison](#m0081)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows](#m0304)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|二重frameの各行は一般化候補だが、resolution用の写像空間APIに依存する。|
|現状の構成|Rowwise comparisons for a double resolution mapping object。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0083"></a>

### m0083 · HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence

|項目|記録|
|---|---|
|分類|C|
|ソース|[DiagonalMappingWeakEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DiagonalMappingWeakEquivalence.lean)|
|追加|2026-10-16T08:48:38+09:00 · `5f020cfcb181`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.resolution_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.DiagonalMappingComparison.liftAction_comparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows](#m0121)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|対角の弱同値比較は一般化候補だが、現行のresolution契約からの独立性を未判定。|
|現状の構成|The actual diagonal resolution Hom comparison is a weak equivalence。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0084"></a>

### m0084 · HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets

|項目|記録|
|---|---|
|分類|B|
|ソース|[DualResolutionTargets.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/DualResolutionTargets.lean)|
|追加|2026-10-16T19:51:40+09:00 · `1127bcd5cab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.DualResolutionTargets.Index`<br>`SerrePositivity.HomotopyFunctionComplex.DualResolutionTargets.liftBase_base`<br>`SerrePositivity.HomotopyFunctionComplex.DualResolutionTargets.instFullFramedIndexFramedBase`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual fibrant target presentations from resolutions in the opposite model。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0085"></a>

### m0085 · HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace

|項目|記録|
|---|---|
|分類|B|
|ソース|[FrameLiftSpace.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FrameLiftSpace.lean)|
|追加|2026-10-16T22:36:37+09:00 · `0babf6dcb65d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FrameLiftSpace.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.FrameLiftSpace.interval`<br>`SerrePositivity.HomotopyFunctionComplex.FrameLiftSpace.kanComplex`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison](#m0086)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison](#m0086)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Derived comparison spaces for actual outer-frame maps over a fixed inner map。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0086"></a>

### m0086 · HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[FrameSquareComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FrameSquareComparison.lean)|
|追加|2026-10-16T22:36:37+09:00 · `0babf6dcb65d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison.interval`<br>`SerrePositivity.HomotopyFunctionComplex.FrameSquareComparison.extension`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Comparing the two actual framed paths of an inner commuting square。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0087"></a>

### m0087 · HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[FramedMappingBifunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FramedMappingBifunctor.lean)|
|追加|2026-10-16T12:40:40+09:00 · `00bdacac7ce7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FramedResolution.raw`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.piZero_naturality_target`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.piZero_map_eq_of_base_eq`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains](#m0091)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains](#m0091)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict Kan-valued bifunctor on actual framed resolutions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0088"></a>

### m0088 · HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization

|項目|記録|
|---|---|
|分類|B|
|ソース|[FramedMappingLocalization.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FramedMappingLocalization.lean)|
|追加|2026-10-16T12:40:40+09:00 · `00bdacac7ce7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FramedResolution.localizedRaw`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.localizedComparisonIso`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.localized_map_eq_of_base_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Natural localization comparison for the framed Kan bifunctor。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0089"></a>

### m0089 · HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[FramedPreChoiceFunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FramedPreChoiceFunctor.lean)|
|追加|2026-10-16T13:15:34+09:00 · `f975a2117df0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FramedPreChoiceFunctor.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.FramedPreChoiceFunctor.projection_trivialFibration`<br>`SerrePositivity.HomotopyFunctionComplex.FramedPreChoiceFunctor.point_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict source precomposition over actual framed contexts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0090"></a>

### m0090 · HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory

|項目|記録|
|---|---|
|分類|B|
|ソース|[FramedResolutionCategory.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FramedResolutionCategory.lean)|
|追加|2026-10-16T12:40:40+09:00 · `00bdacac7ce7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FramedResolution`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.diagonal`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets](#m0084)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace](#m0085)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows](#m0304)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets](#m0084)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison](#m0086)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains](#m0091)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent](#m0274)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor](#m0303)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The category of resolutions with actual outer-frame maps。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0091"></a>

### m0091 · HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains

|項目|記録|
|---|---|
|分類|B|
|ソース|[FramedResolutionChains.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FramedResolutionChains.lean)|
|追加|2026-10-16T12:40:40+09:00 · `00bdacac7ce7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FramedResolution.chainArrow`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.chainHom_reindex`<br>`SerrePositivity.HomotopyFunctionComplex.FramedResolution.chainHom_composition`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Lift arbitrary finite composition chains using their actual frame maps。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0092"></a>

### m0092 · HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreeGeneratorCategories.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreeGeneratorCategories.lean)|
|追加|2026-10-17T06:12:59+09:00 · `c46a1300275c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorCategories.degree_power`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces](#m0094)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces](#m0094)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorCategories.degree_power` — 反復生成元から作る各次数の圏が自由な道の余モナドの反復冪に一致する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0093"></a>

### m0093 · HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreeGeneratorDegeneracies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreeGeneratorDegeneracies.lean)|
|追加|2026-10-17T06:12:59+09:00 · `c46a1300275c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorDegeneracies.degeneracy_intersection_unique`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues](#m0095)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues](#m0095)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorDegeneracies.degeneracy_intersection_unique` — 自由生成元の二つの退化像の交わりは一意な共通の二重退化として表される。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0094"></a>

### m0094 · HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreeGeneratorFaces.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreeGeneratorFaces.lean)|
|追加|2026-10-17T06:26:09+09:00 · `7848305b03c9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorFaces.fixedFace_overlap`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorFaces.fixedFace_overlap` — 自由生成元の面の値が退化像の重なりでも一致する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0095"></a>

### m0095 · HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorLatchingValues

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreeGeneratorLatchingValues.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreeGeneratorLatchingValues.lean)|
|追加|2026-10-17T06:19:50+09:00 · `121e867625d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues.desc_unique`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues.desc_unique` — 全退化像の和への降下は各退化像上の指定値によって一意に決まる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0096"></a>

### m0096 · HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[FreeGeneratorMixedOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreeGeneratorMixedOperators.lean)|
|追加|2026-10-17T06:33:20+09:00 · `9e6b5af1fc1f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorMixedOperators.rawFace`<br>`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorMixedOperators.degeneracy_face_le`<br>`SerrePositivity.HomotopyFunctionComplex.FreeGeneratorMixedOperators.degeneracy_face_gt`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All mixed face-degeneracy equations on the actual fixed-object resolution。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0097"></a>

### m0097 · HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreePathDegeneracyImage.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreePathDegeneracyImage.lean)|
|追加|2026-10-17T05:56:11+09:00 · `f098bda39ab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage.generator_image_intersection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage.generator_image_intersection` — 自由な道の分解の次数二の二つの退化生成元像の交わりを計算する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0098"></a>

### m0098 · HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution

|項目|記録|
|---|---|
|分類|B|
|ソース|[FreePathResolution.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreePathResolution.lean)|
|追加|2026-10-17T04:57:46+09:00 · `8b65d4615c92`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreePathResolution.map`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathResolution.duplicateNatTrans`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathResolution.comonad`|
|直接import元|[CategoryTheory.Quiver.PathObjectTransport](#m0036)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo](#m0099)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation](#m0100)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces](#m0184)|
|宣言参照元|[CategoryTheory.Quiver.PathObjectTransport](#m0036)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces](#m0094)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage](#m0097)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo](#m0099)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation](#m0100)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution](#m0101)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces](#m0184)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The free-path comonad, with explicit generators and all three laws。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0099"></a>

### m0099 · HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo

|項目|記録|
|---|---|
|分類|B|
|ソース|[FreePathResolutionDegreeTwo.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreePathResolutionDegreeTwo.lean)|
|追加|2026-10-17T05:38:16+09:00 · `de6d28b67ae0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreePathResolutionDegreeTwo.lowerZero`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathResolutionDegreeTwo.degeneracyOne_faceTwo`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathResolutionDegreeTwo.degeneracy_overlap`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage](#m0097)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Faces, degeneracies and overlaps in degree two of the actual free-path resolution。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0100"></a>

### m0100 · HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[FreePathResolutionPresentation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreePathResolutionPresentation.lean)|
|追加|2026-10-17T05:10:38+09:00 · `991011af7348`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation.projection_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution](#m0101)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory](#m0203)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories](#m0092)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces](#m0094)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorMixedOperators](#m0096)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution](#m0101)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory](#m0203)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.FreePathResolutionPresentation.projection_naturality` — 自由な道の分解のaugmentationが全次数の単体作用素に関して自然となる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0101"></a>

### m0101 · HomotopicalAlgebra.HomotopyFunctionComplex.FreePathSimplicialResolution

|項目|記録|
|---|---|
|分類|B|
|ソース|[FreePathSimplicialResolution.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/FreePathSimplicialResolution.lean)|
|追加|2026-10-17T05:19:20+09:00 · `c7eed07998d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution.diagram`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution.degree_zero`<br>`SerrePositivity.HomotopyFunctionComplex.FreePathSimplicialResolution.degree_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual augmented free-path simplicial resolution of an arbitrary category。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0102"></a>

### m0102 · HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanLiftAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/KanLiftAction.lean)|
|追加|2026-10-16T08:54:32+09:00 · `9f15f1ab952e`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.KanLiftAction.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.KanLiftAction.comparison_piZero_bijective`<br>`SerrePositivity.HomotopyFunctionComplex.KanLiftAction.piZeroLocalizationEquiv`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence](#m0103)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence](#m0103)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Kan targets for higher resolution-lift actions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0103"></a>

### m0103 · HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanLiftCoherence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/KanLiftCoherence.lean)|
|追加|2026-10-16T09:01:52+09:00 · `0f1706665c37`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.KanLiftCoherence.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.KanLiftCoherence.identity`<br>`SerrePositivity.HomotopyFunctionComplex.KanLiftCoherence.composition`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual interval comparisons for chosen source lifts。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0104"></a>

### m0104 · HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpace

|項目|記録|
|---|---|
|分類|B|
|ソース|[LiftSpace.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LiftSpace.lean)|
|追加|2026-10-16T08:05:19+09:00 · `37ac8bddda2c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.LiftSpace.point`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpace.kanComplex`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpace.localizationIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction](#m0105)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceFunctor](#m0106)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpacePrecomposition](#m0107)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace](#m0311)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction](#m0105)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceFunctor](#m0106)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpacePrecomposition](#m0107)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace](#m0311)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Spaces of lifts of augmented cosimplicial frames。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0105"></a>

### m0105 · HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[LiftSpaceAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LiftSpaceAction.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.LiftSpaceAction.parameterized`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpaceAction.action`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpaceAction.ofLift`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual actions of lift-space simplices on resolution Hom。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0106"></a>

### m0106 · HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpaceFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[LiftSpaceFunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LiftSpaceFunctor.lean)|
|追加|2026-10-16T08:05:19+09:00 · `37ac8bddda2c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.LiftSpace.map`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpace.functor`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpace.projectionNatTrans`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict functoriality of lift spaces in augmented targets。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0107"></a>

### m0107 · HomotopicalAlgebra.HomotopyFunctionComplex.LiftSpacePrecomposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[LiftSpacePrecomposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LiftSpacePrecomposition.lean)|
|追加|2026-10-16T09:23:34+09:00 · `9b98c444ee9c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.LiftSpacePrecomposition.point`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpacePrecomposition.map_projection`<br>`SerrePositivity.HomotopyFunctionComplex.LiftSpacePrecomposition.ofLift`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Source change for actual spaces of augmented lifts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0108"></a>

### m0108 · HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedHomDiagram

|項目|記録|
|---|---|
|分類|A|
|ソース|[LocalizedHomDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LocalizedHomDiagram.lean)|
|追加|2026-10-17T02:44:58+09:00 · `9461ffc74408`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.LocalizedHomDiagram.spaces`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel](#m0250)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel](#m0250)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.HomotopyFunctionComplex.LocalizedHomDiagram.spaces` — 通常の局所化圏の射集合を両変数に自然な離散単体的集合の図式にする。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0109"></a>

### m0109 · HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedMappingBifunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[LocalizedMappingBifunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LocalizedMappingBifunctor.lean)|
|追加|2026-10-16T07:55:13+09:00 · `a29026e2b025`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.localizedResolutionHom_inverts_target`<br>`SerrePositivity.HomotopyFunctionComplex.homotopyMappingReplacementIso`<br>`SerrePositivity.HomotopyFunctionComplex.homotopyMapping_has_representative`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Extending arbitrary-source mapping spaces to all target objects。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0110"></a>

### m0110 · HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[LocalizedResolutionHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/LocalizedResolutionHom.lean)|
|追加|2026-10-16T07:52:11+09:00 · `fcbefc751616`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.localizedResolutionHom`<br>`SerrePositivity.HomotopyFunctionComplex.localizedResolutionHom_map_source_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.localizedResolutionHom_map_target_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedMappingBifunctor](#m0109)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedMappingBifunctor](#m0109)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Source functoriality without functorial factorizations。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0111"></a>

### m0111 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedBiresolutionComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedBiresolutionComparison.lean)|
|追加|2026-10-16T20:21:09+09:00 · `59d542e89f0d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedBiresolutionComparison.functor`<br>`SerrePositivity.HomotopyFunctionComplex.MixedBiresolutionComparison.pair`<br>`SerrePositivity.HomotopyFunctionComplex.MixedBiresolutionComparison.action`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionComparison](#m0125)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionPairs](#m0255)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The mixed action uses the existing raw double Hom diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0112"></a>

### m0112 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedCenterActionWeakEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedCenterActionWeakEquivalence.lean)|
|追加|2026-10-16T20:49:38+09:00 · `52539e1eb0cc`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence.recovery`<br>`SerrePositivity.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence.kanAction_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence.chain_action_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Weak equivalences for the same center and whole-chain mixed actions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0113"></a>

### m0113 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedCenterComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedCenterComparison.lean)|
|追加|2026-10-16T20:43:20+09:00 · `55b9a0eff2b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison.sources`<br>`SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison.kanComparison`<br>`SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison.kanComparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The comparison targets the same whole-center action output。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0114"></a>

### m0114 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedChoiceCoherentIntervals.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedChoiceCoherentIntervals.lean)|
|追加|2026-10-16T14:40:20+09:00 · `78b8b659ef20`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals.Vertex`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals.interval_zero`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentIntervals.interval_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent mixed intervals retaining all four old comparisons and shared endpoints。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0115"></a>

### m0115 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedChoiceCoherentTriangles.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedChoiceCoherentTriangles.lean)|
|追加|2026-10-16T14:46:40+09:00 · `79fe1764d240`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentTriangles.faceEdge`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentTriangles.triangle_face`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceCoherentTriangles.shared_diagonal`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole coherent mixed triangles sharing the same whole diagonal system。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0116"></a>

### m0116 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedChoiceCompatibility.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedChoiceCompatibility.lean)|
|追加|2026-10-16T13:34:33+09:00 · `1972260f2353`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.instModelCategoryFunctorSimplexCategory_serrePositivity_1`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.retainedTriangle_face`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.retainedTriangle_shared_diagonal`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The mixed context diagram retains the original actual mixed comparisons。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0117"></a>

### m0117 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedChoiceFunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedChoiceFunctor.lean)|
|追加|2026-10-16T13:27:39+09:00 · `7c8e969c76b7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.projection_trivialFibration`<br>`SerrePositivity.HomotopyFunctionComplex.MixedChoiceFunctor.point_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One strict diagram for simultaneous source and target contexts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0118"></a>

### m0118 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedDiagonalHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedDiagonalHom.lean)|
|追加|2026-10-16T20:21:09+09:00 · `59d542e89f0d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.obj`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.map`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.map_app`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery](#m0119)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport](#m0120)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery](#m0119)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport](#m0120)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows](#m0121)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor](#m0122)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Two-sided parameterized composition on the actual mixed diagonal Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0119"></a>

### m0119 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomRecovery

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedDiagonalHomRecovery.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedDiagonalHomRecovery.lean)|
|追加|2026-10-16T20:21:09+09:00 · `59d542e89f0d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHomRecovery.constantTargetIso`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHomRecovery.source_pairing`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHomRecovery.target_pairing`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Recover the original one-sided diagonal pairings from the mixed action。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0120"></a>

### m0120 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedDiagonalHomTransport.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedDiagonalHomTransport.lean)|
|追加|2026-10-16T20:34:52+09:00 · `c9f8a2505d2d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.map_id`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.map_comp`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.action_transport`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows](#m0121)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor](#m0122)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor](#m0122)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transport of the mixed action by actual diagram maps。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0121"></a>

### m0121 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedDiagonalRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedDiagonalRows.lean)|
|追加|2026-10-16T20:43:20+09:00 · `55b9a0eff2b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalRows.leftRows`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalRows.left_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalRows.right_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionComparison](#m0125)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Rowwise detection of weak equivalences on the actual mixed Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0122"></a>

### m0122 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedHomBifunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedHomBifunctor.lean)|
|追加|2026-10-16T21:11:41+09:00 · `60697ddba22a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedDiagonalHom.functor`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionPairs](#m0255)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The strict mixed Hom functor on actual pairs of cosimplicial diagrams。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0123"></a>

### m0123 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedLiftActionWeakEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedLiftActionWeakEquivalence.lean)|
|追加|2026-10-16T20:49:38+09:00 · `52539e1eb0cc`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence.domain`<br>`SerrePositivity.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence.action_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence.kanAction_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Arbitrary whole lift families act by weak equivalences。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0124"></a>

### m0124 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedResolutionCenters.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedResolutionCenters.lean)|
|追加|2026-10-16T20:34:52+09:00 · `c9f8a2505d2d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedResolutionCenters.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionCenters.kan_action_parameter`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionCenters.kan_action_transport`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedAction](#m0129)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLifts](#m0302)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual input, output, and lift families over both changing centers。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0125"></a>

### m0125 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedResolutionComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedResolutionComparison.lean)|
|追加|2026-10-16T20:43:20+09:00 · `55b9a0eff2b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedResolutionComparison.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionComparison.augmentation_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionComparison.comparison_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual two-sided frame augmentation is a natural weak equivalence。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0126"></a>

### m0126 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedResolutionInvariance.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedResolutionInvariance.lean)|
|追加|2026-10-16T20:49:38+09:00 · `52539e1eb0cc`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedResolutionInvariance.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionInvariance.lift_map_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionInvariance.strict_action_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Weak equivalences of the actual raw mixed Hom and strict lift actions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0127"></a>

### m0127 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedResolutionKanComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedResolutionKanComparison.lean)|
|追加|2026-10-16T20:43:20+09:00 · `55b9a0eff2b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedResolutionKanComparison.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionKanComparison.piZeroEquiv`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionKanComparison.localizedIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Connecting the actual mixed action output to both existing Kan diagrams。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0128"></a>

### m0128 · HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[MixedResolutionLiftAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/MixedResolutionLiftAction.lean)|
|追加|2026-10-16T20:21:09+09:00 · `59d542e89f0d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.MixedResolutionLiftAction.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionLiftAction.kanAction`<br>`SerrePositivity.HomotopyFunctionComplex.MixedResolutionLiftAction.extends_kanAction`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simultaneous actual resolution lifts in the two variables。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0129"></a>

### m0129 · HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMixedAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/NerveMixedAction.lean)|
|追加|2026-10-16T20:34:52+09:00 · `c9f8a2505d2d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.NerveMixedAction.parameter`<br>`SerrePositivity.HomotopyFunctionComplex.NerveMixedAction.operator`<br>`SerrePositivity.HomotopyFunctionComplex.NerveMixedAction.operator_of_input`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole-chain mixed actions with both moving center transports。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0130"></a>

### m0130 · HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMixedChoices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/NerveMixedChoices.lean)|
|追加|2026-10-16T20:34:52+09:00 · `c9f8a2505d2d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices.leftSystem`<br>`SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices.extendLeft_restrict`<br>`SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices.extendRight_restrict`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual coherent choices for both centers with the original families retained。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0131"></a>

### m0131 · HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveSmallAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/NerveSmallAction.lean)|
|追加|2026-10-16T17:51:14+09:00 · `5840161861db`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.NerveSmallAction.parameter`<br>`SerrePositivity.HomotopyFunctionComplex.NerveSmallAction.inputMap_comp`<br>`SerrePositivity.HomotopyFunctionComplex.NerveSmallAction.outputMap_comp`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Small whole-chain actions with both actual endpoint transports under every simplex operator。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0132"></a>

### m0132 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarAmbientWordComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarAmbientWordComparison.lean)|
|追加|2026-10-17T08:32:16+09:00 · `29fd7a58a5a4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison.degreeEquiv`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison.augmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison.localized_small_iff_words`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual diagonal ambient Hom as a presentation without split vertices。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0133"></a>

### m0133 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarAssociativityCoherence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarAssociativityCoherence.lean)|
|追加|2026-10-17T10:15:58+09:00 · `7e35fee96a74`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence.data`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence.right_second`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence.common_diagonal`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A threefold native composite has a specified associativity disc。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0134"></a>

### m0134 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarAugmentationEquivalences.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarAugmentationEquivalences.lean)|
|追加|2026-10-17T01:20:19+09:00 · `bb54cd3df030`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences.sourceIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences.small_eq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences.small_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Both original simplex augmentations in the ordinary bar evaluation square are inverted。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0135"></a>

### m0135 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarBaseInvariance.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarBaseInvariance.lean)|
|追加|2026-10-17T01:37:45+09:00 · `64bc55bf4c1c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarBaseInvariance.ofBase`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarBaseInvariance.localized_map_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarBaseInvariance.valueIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The strict large ordinary bar inverts weak equivalences in both base variables。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0136"></a>

### m0136 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCenters.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCenters.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCenters.Comma`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCenters.leftSystem_point`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCenters.rightSystem_point`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual contravariant lift centers on a resolution bar comma category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0137"></a>

### m0137 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChainFamily.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChainFamily.lean)|
|追加|2026-10-17T04:13:32+09:00 · `09e54ad25ec0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChainFamily.chain`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChainFamily.cubeFamily_one`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChainFamily.cubeFamily_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All finite ambient chains transferred to the original small value universe。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0138"></a>

### m0138 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceBoundaryExt.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceBoundaryExt.lean)|
|追加|2026-10-17T05:56:11+09:00 · `f098bda39ab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt.hom_ext`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Boundary choices are determined by their entire facet restrictions。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0139"></a>

### m0139 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceBoundaryGluing.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceBoundaryGluing.lean)|
|追加|2026-10-17T06:19:50+09:00 · `121e867625d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing.parameters`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing.boundaryHom`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing.boundaryHom_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing](#m0172)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing](#m0172)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All-degree gluing of actual parameterized choice morphisms。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0140"></a>

### m0140 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceCategory.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceCategory.lean)|
|追加|2026-10-17T04:26:51+09:00 · `e7f3364653ce`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceCategory.Object`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceCategory.projection_full`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceCategory.reindex_full`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory](#m0144)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension](#m0176)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt](#m0138)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory](#m0144)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing](#m0172)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension](#m0176)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces](#m0184)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory](#m0203)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension](#m0210)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual categories of whole parameterized lifts of the original Kan bar action。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0141"></a>

### m0141 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceChainTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceChainTransfer.lean)|
|追加|2026-10-17T04:33:49+09:00 · `0f0e14e64bc0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer.choiceObject`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer.small_zero_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer.small_one_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transfer of entire parameterized morphisms of the relative choice category。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0142"></a>

### m0142 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceComposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceComposition.lean)|
|追加|2026-10-17T04:19:50+09:00 · `47c0de8ad7ff`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceComposition.composite_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceComposition.compose_actionPoint`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceComposition.compositeComparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Composition of entire relative extension spaces over the original base action。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0143"></a>

### m0143 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceMappingSpace.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceMappingSpace.lean)|
|追加|2026-10-17T04:42:45+09:00 · `e2e5f576c0d8`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace.vertex`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace.projection_composition`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace.projection_identity`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual simplicial mapping spaces of relative bar-action lifts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0144"></a>

### m0144 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceSimplicialCategory.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceSimplicialCategory.lean)|
|追加|2026-10-17T04:26:51+09:00 · `e7f3364653ce`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory.functor`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory](#m0203)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict simplicial diagram of categories of relative bar-action lifts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0145"></a>

### m0145 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarChoiceTriangleGluing.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarChoiceTriangleGluing.lean)|
|追加|2026-10-17T05:45:53+09:00 · `ca74aeaecee2`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing.interval`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing.boundaryHom_face1`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing.boundaryHom_face0`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt](#m0138)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)<br>[HomotopicalAlgebra.Simplicial.TriangleDegeneracyParameters](#m0586)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt](#m0138)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Glue three actual parameterized choice morphisms with their endpoint equations。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0146"></a>

### m0146 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarClosedHomDescent.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarClosedHomDescent.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent.target_kan`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent.nativeFamily_substitute`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent.native_restriction_homotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual descent of each whole parameterized action to the original Hom。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0147"></a>

### m0147 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarClosedHomDescentLaws.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarClosedHomDescentLaws.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent.native_identity_homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent.native_composition_homotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Parameterized identity and composition homotopies after Hom descent。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0148"></a>

### m0148 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCommaCone.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCommaCone.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCommaCone.first`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCommaCone.barIndices`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarCommaCone.barCone`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A whole cone inside the ordinary resolution comma category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0149"></a>

### m0149 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCompositionChoices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCompositionChoices.lean)|
|追加|2026-10-17T09:49:11+09:00 · `646b0cb95d2d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionChoices`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionTriangleData`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.comparisonOfCompositionTriangles`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All native composition triangles form a small relative extension space。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0150"></a>

### m0150 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCompositionParameterDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCompositionParameterDiagram.lean)|
|追加|2026-10-17T10:03:40+09:00 · `e455b341e062`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionParameterDiagram`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionParameterPointInterval_zero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionParameterPointInterval_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The strict small restriction diagram of actual native composition triangles。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0151"></a>

### m0151 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCompositionReindex.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCompositionReindex.lean)|
|追加|2026-10-17T09:54:58+09:00 · `b18f89d69395`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositeComparison_reindex`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionTriangle_reindex`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionChoiceFamily_reindex`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual reindexing of the small composition triangle choice space。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0152"></a>

### m0152 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarCompositionReindexLaws.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarCompositionReindexLaws.lean)|
|追加|2026-10-17T09:54:58+09:00 · `b18f89d69395`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionChoices_reindex_id`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionTriangle_family_reindex`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.selectedTriangleReindexComparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Identity, composition, and selected-point laws for composition-choice reindexing。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0153"></a>

### m0153 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalAction.lean)|
|追加|2026-10-17T08:11:58+09:00 · `933d84903b7c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAction.action`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAction.largeFamily_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAction.largeFamily_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The whole diagonal parameter acts by actual maps of lifted small values。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0154"></a>

### m0154 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalAmbientHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalAmbientHom.lean)|
|追加|2026-10-17T08:25:11+09:00 · `7c5e24aa8ffe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom.quotientAt`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom.inclusion`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom.inclusion_transfer`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Ambient Hom and its actual small-vertex retract in the diagonal resolution。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0155"></a>

### m0155 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalClosedAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalClosedAction.lean)|
|追加|2026-10-17T08:11:58+09:00 · `933d84903b7c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction.mapping`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction.nativeFamily_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction.nativeFamily_comp`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Diagonal word action valued in the actual small internal Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0156"></a>

### m0156 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalClosedCompatibility.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalClosedCompatibility.lean)|
|追加|2026-10-17T08:19:31+09:00 · `312d85972ec6`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility.mapping_nativeFamily`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility.mapping_comp`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility.mapping_identity`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The whole diagonal mapping preserves standard composition and native families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0157"></a>

### m0157 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalEvaluation.lean)|
|追加|2026-10-17T08:06:18+09:00 · `819cb7c4a49c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation.parameters`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation.family_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation.family_comp`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual diagonal word families evaluated on the native small bar values。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0158"></a>

### m0158 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalHomAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalHomAugmentation.lean)|
|追加|2026-10-17T08:25:11+09:00 · `7c5e24aa8ffe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation.baseHom`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation.augmentation_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation.localized_small_iff_ambient`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual ambient and small-vertex Hom augmentations to the original base。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0159"></a>

### m0159 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarDiagonalHomRetraction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarDiagonalHomRetraction.lean)|
|追加|2026-10-17T08:25:11+09:00 · `7c5e24aa8ffe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction.sandwich`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction.localized_transfer_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction.localized_inclusion_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|An explicit all-degree Hom retraction without a large simplicial model structure。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0160"></a>

### m0160 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarEvaluatedEndpoint.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarEvaluatedEndpoint.lean)|
|追加|2026-10-16T23:36:02+09:00 · `59633177dfe3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint.SmallNerve`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint.homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint.image_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual small factorization and augmentation square for the other endpoint。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0161"></a>

### m0161 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarEvaluation.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluation.raw`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluation.simplex_operator`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluation.evaluation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation of the actual resolution bar in the small mixed reference Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0162"></a>

### m0162 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarEvaluationEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarEvaluationEquivalence.lean)|
|追加|2026-10-17T01:30:22+09:00 · `db8c43beae3d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence.nerveAugmentation_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence.right_natural_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence.ordinaryRight_natural_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The original ordinary resolution-bar evaluation is inverted。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0163"></a>

### m0163 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFirstAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFirstAction.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstAction.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstAction.action`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstAction.operator`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole first-endpoint actions on the actual bar comma chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0164"></a>

### m0164 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFirstEndpoint.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFirstEndpoint.lean)|
|追加|2026-10-16T23:36:02+09:00 · `59633177dfe3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint.chain_ext`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint.homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint.image_eq`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Identifying the first bar-valued endpoint on all original chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0165"></a>

### m0165 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedAugmentation.lean)|
|追加|2026-10-17T08:25:11+09:00 · `7c5e24aa8ffe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation.sourceProjection`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation.projection`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation.projection_naturality`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The augmentation with literal original base objects at every vertex。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0166"></a>

### m0166 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedChoices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedChoices.lean)|
|追加|2026-10-17T08:06:18+09:00 · `819cb7c4a49c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices.target`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices.action_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedChoices.action_obj`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual coherent choices on the ordinary simplex diagram with fixed objects。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0167"></a>

### m0167 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedRowWordHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedRowWordHom.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom.hom`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom.map_eq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom.localized_augmentation_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual fixed-outer-degree word Hom augmentation is inverted。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0168"></a>

### m0168 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedSource.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedSource.lean)|
|追加|2026-10-17T08:06:18+09:00 · `819cb7c4a49c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedSource.source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedSource.literal`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedSource.literal_eq`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual free resolution with the original base as its literal object set。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0169"></a>

### m0169 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedWordEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedWordEvaluation.lean)|
|追加|2026-10-17T08:06:18+09:00 · `819cb7c4a49c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation.evaluation_map`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation.family_map`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Every ordinary simplex map commutes with the actual fixed-object word evaluation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0170"></a>

### m0170 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFixedWordResolution.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFixedWordResolution.lean)|
|追加|2026-10-17T08:06:18+09:00 · `819cb7c4a49c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution.diagram`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution.identity_left`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution.identity_right`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual diagonal word resolution with fixed literal base objects。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0171"></a>

### m0171 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeAmbientFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeAmbientFamilies.lean)|
|追加|2026-10-17T06:54:50+09:00 · `1d636a0f0857`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies.augmentation_obj`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies.family_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies.family_degeneracy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent ambient families with the original objects as literal endpoints。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0172"></a>

### m0172 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeBoundaryGluing.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeBoundaryGluing.lean)|
|追加|2026-10-17T06:19:50+09:00 · `121e867625d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing.generators`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing.faceDiagram`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing.boundary_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Assemble all faces into a whole free boundary diagram in every degree。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0173"></a>

### m0173 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeChainTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeChainTransfer.lean)|
|追加|2026-10-17T07:02:22+09:00 · `7a2b30b89608`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer.chain`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer.evaluate_zero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer.family_zero`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transfer arbitrary finite chains of actual free-resolution arrows。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0174"></a>

### m0174 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeChainUnits.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeChainUnits.lean)|
|追加|2026-10-17T07:08:24+09:00 · `34545b1cf321`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits.parameterContraction`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits.small_trailing_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits.small_leading_identity`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual endpoint units and unit-boundary formulas for all free-resolution degrees。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0175"></a>

### m0175 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeDegeneracyExtension.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeDegeneracyExtension.lean)|
|追加|2026-10-17T06:19:50+09:00 · `121e867625d7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension.Value`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension.degenerateDiagram_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension.filler_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative free extension preserving every degeneracy in arbitrary degree。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0176"></a>

### m0176 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeDiagramExtension.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeDiagramExtension.lean)|
|追加|2026-10-17T04:51:43+09:00 · `b9e169133b16`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension.target`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension.freeCover`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension.freeCover_projection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces](#m0184)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension](#m0210)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeBoundaryGluing](#m0172)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary](#m0179)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces](#m0184)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension](#m0210)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Extend whole free diagrams while preserving every prescribed parameter。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0177"></a>

### m0177 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeDiagramHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeDiagramHomotopy.lean)|
|追加|2026-10-17T05:32:30+09:00 · `ae308428a4fe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy.interval`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy.comparison_one`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy.comparison_fixed`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt](#m0138)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative interval comparisons of whole free diagrams。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0178"></a>

### m0178 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionAction.lean)|
|追加|2026-10-17T06:54:50+09:00 · `1d636a0f0857`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction.parameters`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction.baseProjection`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction.choicesAt_projection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual ambient arrow families on the entire free resolution。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0179"></a>

### m0179 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionBoundary.lean)|
|追加|2026-10-17T06:26:09+09:00 · `7848305b03c9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary.face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary.boundary`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionBoundary.boundary_face`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual next free-resolution boundary from the preceding face equations。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0180"></a>

### m0180 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionChoices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionChoices.lean)|
|追加|2026-10-17T06:39:33+09:00 · `0ac50cca7f3c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices.diagram`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices.projection_zero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices.projection_eq_augmentation`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual coherent choices on the entire free resolution of the original base。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0181"></a>

### m0181 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionComparison.lean)|
|追加|2026-10-17T05:32:30+09:00 · `ae308428a4fe`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison.startGenerators`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison.comparison_degeneracy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison.comparison_projection`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The first free-resolution comparison, constant on the entire degeneracy image。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0182"></a>

### m0182 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionDegeneracyValues.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionDegeneracyValues.lean)|
|追加|2026-10-17T06:26:09+09:00 · `7848305b03c9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues.sigma`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues.prescribedValue`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues.prescribedValue_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.ReversedSimplexParameters](#m0550)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.Simplicial.ReversedSimplexParameters](#m0550)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual degenerate values and their all-degree intersection compatibility。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0183"></a>

### m0183 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionDegenerateBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionDegenerateBoundary.lean)|
|追加|2026-10-17T06:33:20+09:00 · `9e6b5af1fc1f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary.boundary_degeneracy_facet`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary.boundary_degeneracy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep](#m0188)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The prescribed all-degree degeneracies restrict to the actual boundary。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0184"></a>

### m0184 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionFaces.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionFaces.lean)|
|追加|2026-10-17T04:57:46+09:00 · `8b65d4615c92`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces.faceZero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces.degeneracy_faceZero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionFaces.degeneracy_faceOne`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison](#m0181)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary](#m0191)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The first two free-resolution faces of the actual choice-cover functor。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0185"></a>

### m0185 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionMixedFaces.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionMixedFaces.lean)|
|追加|2026-10-17T06:33:20+09:00 · `9e6b5af1fc1f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces.raw_face_law`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces.facet_gt`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces.facet_equation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Every facet of a prescribed degenerate choice diagram。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0186"></a>

### m0186 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionNaturalChoice.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionNaturalChoice.lean)|
|追加|2026-10-17T06:46:13+09:00 · `b5aca038f600`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice.source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice.augmentation_comparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice.augmentation_eq_standard`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual coherent free choices as a natural transformation on the usual simplex category。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0187"></a>

### m0187 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionSeed.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionSeed.lean)|
|追加|2026-10-17T06:39:33+09:00 · `0ac50cca7f3c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed.point`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed.one_degeneracy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed.seed`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual initial coherent pair for the free choice resolution。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0188"></a>

### m0188 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionStep.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionStep.lean)|
|追加|2026-10-17T06:33:20+09:00 · `9e6b5af1fc1f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep.inclusion`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep.filler_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionStep.filler_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower](#m0189)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Raise the degree of the coherent free choice diagram。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0189"></a>

### m0189 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeResolutionTower.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeResolutionTower.lean)|
|追加|2026-10-17T06:34:36+09:00 · `0d66760a23a3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower.Pair`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower.diagram_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeResolutionTower.diagram_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionChoices](#m0180)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionSeed](#m0187)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Iterate the relative free-resolution step with all coherence equations。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0190"></a>

### m0190 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeTransferredFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeTransferredFamilies.lean)|
|追加|2026-10-17T06:54:50+09:00 · `1d636a0f0857`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies.ofFamily`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies.transferred_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies.transferred_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transfer the actual coherent ambient families to the small object models。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0191"></a>

### m0191 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeTriangleBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeTriangleBoundary.lean)|
|追加|2026-10-17T05:38:16+09:00 · `de6d28b67ae0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary.source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary.double_degeneracy_edge02`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleBoundary.double_degeneracy_edge12`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing](#m0194)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual triangle edges and their vertex and degeneracy overlaps。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0192"></a>

### m0192 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeTriangleDegeneracy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeTriangleDegeneracy.lean)|
|追加|2026-10-17T05:56:11+09:00 · `f098bda39ab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy.inclusion`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy.boundary_degeneracyZero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy.boundary_degeneracyOne`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Prescribed degenerate triangles restrict to the actual glued boundary。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0193"></a>

### m0193 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeTriangleFiller.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeTriangleFiller.lean)|
|追加|2026-10-17T05:56:11+09:00 · `f098bda39ab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller.parameters`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller.filler_degeneracyZero`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller.filler_degeneracyOne`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A two-simplex filler preserving both whole degeneracy images。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0194"></a>

### m0194 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeTriangleGluing.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeTriangleGluing.lean)|
|追加|2026-10-17T05:45:53+09:00 · `ca74aeaecee2`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing.edgeA`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing.boundary_face0`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTriangleGluing.boundary_projection`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual free triangle boundary diagram with all original parameters。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0195"></a>

### m0195 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarFreeWordChainTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarFreeWordChainTransfer.lean)|
|追加|2026-10-17T07:29:06+09:00 · `01b49826a79d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer.chain`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer.ofPath_ofInterval`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer.family_ofInterval`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All free-resolution degrees with actual word-parameter chain transfer。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0196"></a>

### m0196 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarHomSections.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarHomSections.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections.source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections.ambient_surjective`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomSections.small_surjective`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Split epimorphisms on the Hom augmentations, in every simplicial degree。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0197"></a>

### m0197 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarHomotopyDescent.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarHomotopyDescent.lean)|
|追加|2026-10-17T03:32:15+09:00 · `d9187beee7ad`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent.functor`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent.presentation_map_eq_of_base_eq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent.presentation_map_isIso_of_base_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict descent on the original base with homotopy-class morphisms。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0198"></a>

### m0198 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarLabelSurjectivity.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarLabelSurjectivity.lean)|
|追加|2026-10-17T02:48:23+09:00 · `bbdf14ce7475`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity.raw_label_surjective`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity.coarseLiftIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity.coarseProjection_comparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Every ordinary localized morphism is represented by an actual bar simplex。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0199"></a>

### m0199 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarMappingClasses.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarMappingClasses.lean)|
|追加|2026-10-17T02:44:58+09:00 · `9461ffc74408`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingClasses.augmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingClasses.coarseQuotient`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingClasses.coarseProjection`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A natural ordinary mapping-class label on the whole resolution bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0200"></a>

### m0200 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarMappingComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarMappingComparison.lean)|
|追加|2026-10-17T01:37:45+09:00 · `64bc55bf4c1c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison.small_map_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison.resolutionIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarMappingComparison.zeroIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Natural comparison of the ordinary bar with the small mapping diagrams。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0201"></a>

### m0201 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarNerveBridge.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarNerveBridge.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarNerveBridge.rawBridge`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarNerveBridge.homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarNerveBridge.image_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The total-element nerve comparison lands in the original ordinary bar。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0202"></a>

### m0202 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarNormalizedCompositionTriangle.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarNormalizedCompositionTriangle.lean)|
|追加|2026-10-17T10:52:25+09:00 · `880c661b5d70`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.normalizedCompositionTriangle`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.normalizedNativeCompositionComparison_reindex`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.normalizeCompositionTriangleComparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Native composition triangles now admit a strictly parameter-natural choice。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0203"></a>

### m0203 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarParameterChoiceCategory.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarParameterChoiceCategory.lean)|
|追加|2026-10-17T06:46:13+09:00 · `b5aca038f600`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory.diagram`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory.baseProjection`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarParameterChoiceCategory.projection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionNaturalChoice](#m0186)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The simplicial choice-category diagram with a fixed whole parameter。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0204"></a>

### m0204 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarPiZero.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarPiZero.lean)|
|追加|2026-10-17T02:58:23+09:00 · `b89d729dcc44`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarPiZero.entry_localized_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarPiZero.piZeroEquiv_mk`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarPiZero.piZeroEquiv_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual components of the ordinary resolution bar are ordinary localized morphisms。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0205"></a>

### m0205 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarReference.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarReference.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReference.reference`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReference.smallAction_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReference.section_evaluation_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation on the actual identity-reference section of the resolution bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0206"></a>

### m0206 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarReferenceRowHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarReferenceRowHomotopy.lean)|
|追加|2026-10-17T01:30:22+09:00 · `db8c43beae3d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy.bridge`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy.referenceComposite`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy.reference_factorization`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The labelled reference-to-row cone gives an actual bar-valued interval。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0207"></a>

### m0207 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarReferenceRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarReferenceRows.lean)|
|追加|2026-10-17T01:30:22+09:00 · `db8c43beae3d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows.raw`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows.rowElements`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReferenceRows.comparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Labelled reference-to-row comparison on the original small raw simplex category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0208"></a>

### m0208 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRelativeComposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRelativeComposition.lean)|
|追加|2026-10-17T09:43:15+09:00 · `a5cdb28eea6b`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionSquare`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionSquare_diagonal`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.compositionComparison_substitute`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Two selected native comparisons compose through one specified square。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0209"></a>

### m0209 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRelativeCompositionTriangle.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRelativeCompositionTriangle.lean)|
|追加|2026-10-17T09:43:15+09:00 · `a5cdb28eea6b`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.composite_augmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.nativeCompositionComparison_base`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.nativeUnitComparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual composition triangle retains all three Hom comparisons。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0210"></a>

### m0210 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRelativeFreeDiagramExtension.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRelativeFreeDiagramExtension.lean)|
|追加|2026-10-17T04:51:43+09:00 · `b9e169133b16`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension.Prescribed`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension.extendFunctor_restriction`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension.extendFunctor_projection`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDegeneracyExtension](#m0175)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleFiller](#m0193)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Extend free diagrams while fixing prescribed generators over the whole parameter。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0211"></a>

### m0211 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRelativeHomDescent.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRelativeHomDescent.lean)|
|追加|2026-10-17T09:35:05+09:00 · `6ac6247d8399`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.parameterAugmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.nativeFamily_substitute`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.native_relative_extension`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative descent choices for the actual whole word action。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0212"></a>

### m0212 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRelativeNativeComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRelativeNativeComparison.lean)|
|追加|2026-10-17T09:37:24+09:00 · `146b97395294`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.nativeRestrictionComparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.nativeRestrictionComparison_substitute`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent.native_relative_comparison_extension`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Native interval comparisons decoded from the relative descent space。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0213"></a>

### m0213 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarReplacementComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarReplacementComparison.lean)|
|追加|2026-10-17T01:37:45+09:00 · `64bc55bf4c1c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReplacementComparison.baseComparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReplacementComparison.refinementIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarReplacementComparison.presentationIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A natural comparison with the original replacement mapping diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0214"></a>

### m0214 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRetractSystem.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRetractSystem.lean)|
|追加|2026-10-17T03:50:44+09:00 · `41479ac9d7b0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.small`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.transferred_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.parameter_extension`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict objectwise retracts and all-dimensional relative arrow choices。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0215"></a>

### m0215 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRetractTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRetractTransfer.lean)|
|追加|2026-10-17T04:00:54+09:00 · `40f85bde91b4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.transferArrow`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.smallTransferCompositionHomotopy_left_id`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem.smallTransferCompositionHomotopy_right_id`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transfer of actual ambient arrows with constant unit comparison intervals。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0216"></a>

### m0216 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRightEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRightEvaluation.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRightEvaluation.padded_reference`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRightEvaluation.right_isIso_iff_evaluation`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The original right leg is invertible exactly when the ordinary evaluation is。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0217"></a>

### m0217 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarRowDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarRowDiagram.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRowDiagram.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRowDiagram.left_bar_recovery`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRowDiagram.right_bar_recovery`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One strict diagram of the underlying row cone maps over all nerve simplices。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0218"></a>

### m0218 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSimplexCone.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSimplexCone.lean)|
|追加|2026-10-16T23:01:05+09:00 · `5ae9d03165cf`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSimplexCone.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSimplexCone.elementArrow`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSimplexCone.arrow_raw_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Each actual bar simplex maps to its exact evaluated row presentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0219"></a>

### m0219 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSmallAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSmallAction.lean)|
|追加|2026-10-17T01:48:15+09:00 · `679d11646bb7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallAction.transported`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallAction.square_homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallAction.arrow_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual small arrow representatives for the strict large bar action。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0220"></a>

### m0220 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSmallFreeChainTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSmallFreeChainTransfer.lean)|
|追加|2026-10-17T07:02:22+09:00 · `7a2b30b89608`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer.family`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer.zero_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer.one_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Native small parameter families for arbitrary actual free-resolution chains。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0221"></a>

### m0221 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSmallFreeWordChainTransfer.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSmallFreeWordChainTransfer.lean)|
|追加|2026-10-17T07:29:06+09:00 · `01b49826a79d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer.family`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer.zero_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer.family_ofInterval`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Native small parameter families for arbitrary actual free-resolution chains。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0222"></a>

### m0222 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSmallReference.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSmallReference.lean)|
|追加|2026-10-17T01:48:15+09:00 · `679d11646bb7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference.value`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference.homEquiv`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallReference.small_localizedHom`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual weak maps from the large bar to small Kan reference values。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0223"></a>

### m0223 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSmallSubcomplex.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSmallSubcomplex.lean)|
|追加|2026-10-17T02:01:36+09:00 · `af5e0ec787ef`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex.ambient`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex.smallInclusion`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex.smallInclusion_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|An actual small homotopy-equivalent subcomplex inside each Kan bar value。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0224"></a>

### m0224 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceContraction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceContraction.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction.baseReverseIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction.word_augmentation_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction.small_augmentation_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual source and small-vertex augmentations are localized isomorphisms。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0225"></a>

### m0225 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceExtraDegeneracy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceExtraDegeneracy.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy.augmented`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy.extraDegeneracy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy.localized_augmentation_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Singleton extra degeneracies on the actual forward source Hom augmentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0226"></a>

### m0226 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceExtraOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceExtraOperators.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators.fixedForwardFace`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators.degeneracy_succ_singleton`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators.projection_zero_map`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Exact-object face operators on singleton free paths。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0227"></a>

### m0227 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceHom.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom.hom`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom.augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators](#m0228)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual outer source Hom simplicial set and its base augmentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0228"></a>

### m0228 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceOperators.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceOperators.diagram_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceOperators.forward_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceOperators.forward_degeneracy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators](#m0226)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual face and degeneracy operators on the fixed-object source。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0229"></a>

### m0229 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceSection.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceSection.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection.section_`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection.section_comp_augmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceSection.augmentation_surjective`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A simplicial section on each Hom of the actual source augmentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0230"></a>

### m0230 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarSourceWordEmbedding.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarSourceWordEmbedding.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding.ambient`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding.ambient_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding.small_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections](#m0196)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual source Hom maps into ambient and small-vertex word Hom。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0231"></a>

### m0231 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarTotalCone.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarTotalCone.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalCone.Index`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalCone.cone_arrow`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalCone.row_label`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The whole labelled cone with changing row degree。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0232"></a>

### m0232 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarTotalEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarTotalEvaluation.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation.rowBase`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation.comparison_degree`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The labelled total cone factors through the same small evaluation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0233"></a>

### m0233 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarTotalHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarTotalHomotopy.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy.firstMap`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy.homotopy`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy.image_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual nerve homotopy of the whole labelled total comparison。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0234"></a>

### m0234 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarTripleComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarTripleComparison.lean)|
|追加|2026-10-17T10:15:58+09:00 · `7e35fee96a74`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTripleComparison.wordComp`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTripleComparison.rightOuterTriangle`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTripleComparison.rightInnerTriangle`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Four actual comparison intervals for a threefold native composite。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0235"></a>

### m0235 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarUnitCoherence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarUnitCoherence.lean)|
|追加|2026-10-17T10:30:03+09:00 · `a36d94353ac3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitCoherence.leftData`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitCoherence.left_retains_triangle`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitCoherence.right_retains_triangle`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Native composition with the unit retains both selected comparison edges。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0236"></a>

### m0236 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarUnitTriangles.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarUnitTriangles.lean)|
|追加|2026-10-17T10:30:03+09:00 · `a36d94353ac3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitTriangles.identityWord`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitTriangles.leftReturn_comparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarUnitTriangles.rightReturn_comparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Preserve the native composition and unit comparisons in unit triangles。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0237"></a>

### m0237 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordAction.lean)|
|追加|2026-10-17T07:45:39+09:00 · `3ff83b21eecb`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordAction.hom`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordAction.family_identity`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordAction.family_comp`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simplicial word-arrow families act on the native small ordinary bar values。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0238"></a>

### m0238 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordActionOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordActionOperators.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators.family_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators.family_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All free-resolution operator laws on native small word-arrow action families。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0239"></a>

### m0239 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordChainFamily.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordChainFamily.lean)|
|追加|2026-10-17T07:29:06+09:00 · `01b49826a79d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordChainFamily.chain`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordChainFamily.family_ofInterval`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordChainFamily.smallFamily_ofInterval`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual word-parameter chain families and their small transfers。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0240"></a>

### m0240 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordContraction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordContraction.lean)|
|追加|2026-10-17T07:25:19+09:00 · `2efc3cce9602`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordContraction.wordEval`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordContraction.family_over`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordContraction.family_section`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual word contractions of the ordinary bar retracts。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0241"></a>

### m0241 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordDiagonalEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordDiagonalEquivalence.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence.diagonal_augmentation_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence.augmentation_isIso_iff_source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence.small_augmentation_isIso_iff_source`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual diagonal word comparison is inverted without a large SSet model structure。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0242"></a>

### m0242 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordEvaluationOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordEvaluationOperators.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators.evaluation_face`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators.evaluation_degeneracy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All free-resolution faces and degeneracies commute with the actual word evaluation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0243"></a>

### m0243 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordPresentation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordPresentation.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordPresentation.realization`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordPresentation.smallEvaluation_map`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordPresentation.largeEvaluation_transferred`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual presented word-category evaluation on the ordinary bar retracts。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0244"></a>

### m0244 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordResolution.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordResolution.lean)|
|追加|2026-10-17T07:58:03+09:00 · `242f0f56cea2`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordResolution.source`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordResolution.projection`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordResolution.projection_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedSource](#m0168)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual augmented bisimplicial word resolution of the ordinary bar base。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0245"></a>

### m0245 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordRowMaps.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordRowMaps.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowMaps.row`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowMaps.rowMap_comp`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowMaps.rows`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All outer simplex operators act on the actual word Hom rows。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0246"></a>

### m0246 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordRows.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows.targetRows`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows.targetDiagonalIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows.toSource`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The augmented bisimplicial word Hom diagram, natural in every outer operator。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0247"></a>

### m0247 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryBarWordRowsDiagonal.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryBarWordRowsDiagonal.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal.comparisonIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal.toSource_app`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal.augmentation_factorization`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The augmented row diagonal is the actual previously constructed word Hom。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0248"></a>

### m0248 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryKanBarMappingClasses.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryKanBarMappingClasses.lean)|
|追加|2026-10-17T03:11:25+09:00 · `41f5c16cf8d9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses.functor`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses.piZeroEquiv_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses.map_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Natural ordinary morphism labels on the actual Kan resolution bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0249"></a>

### m0249 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryKanBarQuotient.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryKanBarQuotient.lean)|
|追加|2026-10-17T03:16:09+09:00 · `5adb629cbaca`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarQuotient.QuotientData`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarQuotient.piZeroEquiv_comparison`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryKanBarQuotient.piZeroEquiv_naturality`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The complete output of a small finite-boundary quotient of the Kan bar。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0250"></a>

### m0250 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryMappingClassLabel.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryMappingClassLabel.lean)|
|追加|2026-10-17T02:44:58+09:00 · `9461ffc74408`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryMappingClassLabel.fraction_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryMappingClassLabel.label_base`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryMappingClassLabel.comparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Ordinary localized morphisms label every raw mixed resolution simplex。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0251"></a>

### m0251 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryQuotientPiZero.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryQuotientPiZero.lean)|
|追加|2026-10-17T03:06:56+09:00 · `963469946d86`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryQuotientPiZero.piZeroLabel`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryQuotientPiZero.smallPiZeroEquiv_naturality`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryQuotientPiZero.smallProjection_factorization`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Every label-preserving stable bar quotient has the same actual components。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0252"></a>

### m0252 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryRawLabelHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryRawLabelHomotopy.lean)|
|追加|2026-10-17T02:58:23+09:00 · `b89d729dcc44`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy.map_eq_of_label_eq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy.edgeOfLabelEq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy.entry_component_eq`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Equal localized labels are joined by an actual mixed resolution edge。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0253"></a>

### m0253 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryResolutionBar.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryResolutionBar.lean)|
|追加|2026-10-16T22:46:13+09:00 · `cd8952ad92b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.functor`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.leftAnodyneIso`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.leftAnodyneIso_hom`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict ordinary-resolution bar with an actual comparison from the original framed bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0254"></a>

### m0254 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryResolutionBarReduction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryResolutionBarReduction.lean)|
|追加|2026-10-16T22:54:15+09:00 · `72407006ad64`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.ordinaryMiddle`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.right_image_isIso_iff`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionBar.right_natural_image_isIso_iff`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Reduction of the original right comparison to ordinary resolutions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0255"></a>

### m0255 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionPairs

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryResolutionPairs.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryResolutionPairs.lean)|
|追加|2026-10-16T22:46:13+09:00 · `cd8952ad92b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs.Index`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs.raw_eq`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs.raw_map`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel](#m0250)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel](#m0250)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The same raw mixed Hom on ordinary resolution pairs。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0256"></a>

### m0256 · HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[OrdinaryResolutionRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/OrdinaryResolutionRows.lean)|
|追加|2026-10-16T22:46:13+09:00 · `cd8952ad92b3`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionRows.rows`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionRows.commaAugmentation`<br>`SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionRows.raw_augmentation_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All original frame rows form a strict diagram inside the ordinary resolution comma category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0257"></a>

### m0257 · HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[PostChainKanParameter.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/PostChainKanParameter.lean)|
|追加|2026-10-16T11:08:26+09:00 · `d612fe0bf80f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.PostChainKanParameter.parameter`<br>`SerrePositivity.HomotopyFunctionComplex.PostChainKanParameter.fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.PostChainKanParameter.action_cut`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A Kan parameter retaining all selected cut triangles of a finite chain。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0258"></a>

### m0258 · HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing

|項目|記録|
|---|---|
|分類|B|
|ソース|[PostChainReindexing.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/PostChainReindexing.lean)|
|追加|2026-10-16T11:15:21+09:00 · `462a22b3c87c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.PostChainReindexing.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.PostChainReindexing.comparison_cut`<br>`SerrePositivity.HomotopyFunctionComplex.PostChainReindexing.reindexHomotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Selecting and repeating cut comparisons of a fixed finite chain。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0259"></a>

### m0259 · HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[PostChoiceFunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/PostChoiceFunctor.lean)|
|追加|2026-10-16T13:06:48+09:00 · `25a7578eda56`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.PostChoiceFunctor.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.PostChoiceFunctor.projection_trivialFibration`<br>`SerrePositivity.HomotopyFunctionComplex.PostChoiceFunctor.point_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict small-valued functor for all external postcomposition contexts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0260"></a>

### m0260 · HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain

|項目|記録|
|---|---|
|分類|B|
|ソース|[PostCompositionChain.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/PostCompositionChain.lean)|
|追加|2026-10-16T11:08:26+09:00 · `d612fe0bf80f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.PostCompositionChain.choiceCast`<br>`SerrePositivity.HomotopyFunctionComplex.PostCompositionChain.fixed_boundary`<br>`SerrePositivity.HomotopyFunctionComplex.PostCompositionChain.action_cut`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simultaneous comparisons at all cuts of a finite composition chain。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0261"></a>

### m0261 · HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient

|項目|記録|
|---|---|
|分類|B|
|ソース|[PresentationKernelQuotient.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/PresentationKernelQuotient.lean)|
|追加|2026-10-17T03:24:44+09:00 · `9a746c831759`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient.reference`<br>`SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient.baseComparisonIso`<br>`SerrePositivity.HomotopyFunctionComplex.PresentationKernelQuotient.map_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A proved small finite-boundary kernel on the full presentation index。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0262"></a>

### m0262 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/BoundaryHom.lean)|
|追加|2026-10-16T08:48:38+09:00 · `a73ee69d3a86`|
|主な公開宣言|`SerrePositivity.Reedy.BoundaryHom.iso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalMatching](#m0386)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalMatching](#m0386)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.BoundaryHom.iso` — latching側の余極限を反変Homでmatching側の極限へ移す同型を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0263"></a>

### m0263 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Elements

|項目|記録|
|---|---|
|分類|A|
|ソース|[Elements.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/Elements.lean)|
|追加|2026-10-16T13:43:22+09:00 · `1de52e9af25a`|
|主な公開宣言|`SerrePositivity.Reedy.elementsReedy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite](#m0264)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentFamily](#m0466)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite](#m0264)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence](#m0265)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentFamily](#m0466)<br>[HomotopicalAlgebra.Simplicial.SimplexIndexFinite](#m0557)<br>[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)<br>[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)<br>[HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal](#m0560)<br>[HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting](#m0561)<br>[HomotopicalAlgebra.Simplicial.SimplexNaturalMatching](#m0562)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.elementsReedy` — Reedy圏上の図式の要素の圏にReedy構造を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0264"></a>

### m0264 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite

|項目|記録|
|---|---|
|分類|A|
|ソース|[ElementsFinite.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/ElementsFinite.lean)|
|追加|2026-10-16T13:49:39+09:00 · `c5b8792f501b`|
|主な公開宣言|`SerrePositivity.Reedy.elementsLatchingIndex_finite`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence](#m0265)<br>[HomotopicalAlgebra.Simplicial.SimplexIndexFinite](#m0557)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence](#m0265)<br>[HomotopicalAlgebra.Simplicial.SimplexIndexFinite](#m0557)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.elementsLatchingIndex_finite` — 要素の圏のlatching添字の有限性を元の境界の有限性から導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0265"></a>

### m0265 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[ElementsMatchingEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/ElementsMatchingEquivalence.lean)|
|追加|2026-10-16T13:58:49+09:00 · `95d8d9bbb600`|
|主な公開宣言|`SerrePositivity.Reedy.elementsLatchingOpEquivalence`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.elementsLatchingOpEquivalence` — 要素の圏における双対latching添字の実際の圏同値を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0266"></a>

### m0266 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOppositeEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[IndexOppositeEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/IndexOppositeEquivalence.lean)|
|追加|2026-10-16T08:48:38+09:00 · `a73ee69d3a86`|
|主な公開宣言|`SerrePositivity.Reedy.matchingOpEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom](#m0262)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom](#m0262)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.matchingOpEquivalence` — 反対圏を取ることで対応するReedy境界添字の圏同値を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0267"></a>

### m0267 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.PrescribedLowerStep

|項目|記録|
|---|---|
|分類|A|
|ソース|[PrescribedLowerStep.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/PrescribedLowerStep.lean)|
|追加|2026-10-16T14:21:16+09:00 · `c9d850e647cb`|
|主な公開宣言|`SerrePositivity.Reedy.PrescribedLowerStep.Data.assemble`|
|直接import元|[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.PrescribedLowerStep.Data.assemble` — 新しい次数の指定セルと既存の低次数の図式を自然な一つの低次数系に貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0268"></a>

### m0268 · HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.RelativeLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeLifting.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/Reedy/RelativeLifting.lean)|
|追加|2026-10-16T14:15:37+09:00 · `9dc93b11a0f3`|
|主な公開宣言|`SerrePositivity.Reedy.RelativeLifting.liftStruct`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Reedy.RelativeLifting.liftStruct` — 指定済みの低次数の持ち上げを保持するReedy持ち上げを構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0269"></a>

### m0269 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementBarAnodyneComparison.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementBarAnodyneComparison.lean)|
|追加|2026-10-16T19:20:01+09:00 · `42d73f5277b5`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryLeftAnodyneIso`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryLeftAnodyneIso_hom_app`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Natural anodyne-localized comparison for the actual auxiliary left bar leg。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0270"></a>

### m0270 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementBarCandidate.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementBarCandidate.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryBar`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryBar_degree`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict auxiliary bar candidate on both undecorated base variables。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0271"></a>

### m0271 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementBarComparisonSpan.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementBarComparisonSpan.lean)|
|追加|2026-10-16T19:00:46+09:00 · `8f58d0eb8b63`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryMiddle`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliarySection`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliarySection_retract`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|An actual natural span comparing replacement mapping spaces and the strict auxiliary bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0272"></a>

### m0272 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementBarLeftContraction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementBarLeftContraction.lean)|
|追加|2026-10-16T19:10:22+09:00 · `1a0688723145`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryLeftHomotopy`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.auxiliaryLeft_has_homotopyInverse`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The chosen left comparison leg has an actual simplicial homotopy inverse。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0273"></a>

### m0273 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementMappingBifunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementMappingBifunctor.lean)|
|追加|2026-10-16T18:26:10+09:00 · `41280dffcf32`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.hom`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.piZero_naturality_source`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.piZero_naturality_target`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Small Kan mapping spaces on actual source and target replacement presentations。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0274"></a>

### m0274 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementMappingDescent.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementMappingDescent.lean)|
|追加|2026-10-16T18:26:10+09:00 · `41280dffcf32`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.Index`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.descentComparison_isIso`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.descentComparisonIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate](#m0270)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate](#m0270)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simultaneous ordinary descent of actual small replacement mapping spaces。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0275"></a>

### m0275 · HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization

|項目|記録|
|---|---|
|分類|B|
|ソース|[ReplacementMappingLocalization.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ReplacementMappingLocalization.lean)|
|追加|2026-10-16T18:26:10+09:00 · `41280dffcf32`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.localized_source_map_eq`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.uncurried_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.ReplacementMapping.localized_uncurried_map_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent](#m0274)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate](#m0270)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent](#m0274)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Independence of both actual replacement maps on full localized mapping spaces。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0276"></a>

### m0276 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowActionFunctors.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowActionFunctors.lean)|
|追加|2026-10-16T17:51:14+09:00 · `5840161861db`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors.targetResolution`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors.output_map`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionFunctors.transport`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The two strict endpoint functors underlying actual resolution-lift actions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0277"></a>

### m0277 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowActionTransport.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowActionTransport.lean)|
|追加|2026-10-16T17:51:14+09:00 · `5840161861db`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport.kan`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowActionTransport.kan_transport`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual action transport along arbitrary simultaneous changes of centers and resolutions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0278"></a>

### m0278 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowComparisonEndpoints.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowComparisonEndpoints.lean)|
|追加|2026-10-16T15:57:48+09:00 · `2e786e3d21f9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints.parameter`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints.left_recover`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints.right_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual all-center comparison endpoints retaining the old whole tuple interpolations。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0279"></a>

### m0279 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowCylinderBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowCylinderBoundary.lean)|
|追加|2026-10-16T16:06:38+09:00 · `da59b69519b7`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary.interval`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary.extend_one`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary.extend_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFaces](#m0280)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit](#m0281)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One actual all-center cylinder boundary with both original endpoint systems fixed。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0280"></a>

### m0280 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFaces

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowCylinderFaces.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowCylinderFaces.lean)|
|追加|2026-10-16T16:24:53+09:00 · `6a4960a942c1`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces.zero`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFaces.one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual standard faces of the glued all-center cylinder boundary。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0281"></a>

### m0281 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowCylinderFamilyFit.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowCylinderFamilyFit.lean)|
|追加|2026-10-16T16:14:50+09:00 · `1259086cfc03`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit.zero_evaluate`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit.extendFamilies_evaluate`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit.extendFamilies_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole cylinder fit derived from the actual two endpoints and entire vertex restriction。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0282"></a>

### m0282 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowDiagram.lean)|
|追加|2026-10-16T15:09:35+09:00 · `673dd59a1084`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram.coherentContext`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowDiagram.coherentContext_component`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One small lift-space diagram for all central base arrows at once。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0283"></a>

### m0283 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowElementary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowElementary.lean)|
|追加|2026-10-16T15:57:48+09:00 · `2e786e3d21f9`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowElementary.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowElementary.pre_left`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowElementary.pre_right`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The original pre/postcomparison endpoints inside the all-center arrow system。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0284"></a>

### m0284 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowParameters.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowParameters.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters.parameters`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters.system_evaluate`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowParameters.system_compatibility`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All-center coherent families with the actual moving factorization parameter。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0285"></a>

### m0285 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowSelectedIntervals.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowSelectedIntervals.lean)|
|追加|2026-10-16T16:24:53+09:00 · `6a4960a942c1`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals.vertex_lifted`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals.pre_fit`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals.pre_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The already selected pre/post intervals satisfy the actual whole cylinder boundary。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0286"></a>

### m0286 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowTupleCoherence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowTupleCoherence.lean)|
|追加|2026-10-16T15:32:44+09:00 · `fb287c15ee25`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence.bigTuples`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence.vertex_component`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTupleCoherence.simplex_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One all-center coherent family retaining the original tuple interpolations。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0287"></a>

### m0287 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionArrowTuples.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionArrowTuples.lean)|
|追加|2026-10-16T15:32:44+09:00 · `fb287c15ee25`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples.vertexData`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionArrowTuples.inclusion_mono`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The old strict lift tuple and vertex boundary diagrams over all centers。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0288"></a>

### m0288 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarCenters.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarCenters.lean)|
|追加|2026-10-16T21:02:18+09:00 · `5d02b7b07e52`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarCenters.Comma`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarCenters.leftSystem_point`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarCenters.rightSystem_point`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual contravariant lift centers on a resolution bar comma category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0289"></a>

### m0289 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarConeDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarConeDiagram.lean)|
|追加|2026-10-16T22:28:29+09:00 · `feb5b6e86d81`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarConeDiagram.forgetLabels`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarConeDiagram.left_recovery`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarConeDiagram.right_recovery`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One strict underlying cone diagram on the actual bar simplex category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0290"></a>

### m0290 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarEvaluation.lean)|
|追加|2026-10-16T21:02:18+09:00 · `5d02b7b07e52`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarEvaluation.raw`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarEvaluation.simplex_operator`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarEvaluation.evaluation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation of the actual resolution bar in the small mixed reference Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0291"></a>

### m0291 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarFirstAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarFirstAction.lean)|
|追加|2026-10-16T21:02:18+09:00 · `5d02b7b07e52`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFirstAction.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFirstAction.action`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFirstAction.operator`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole first-endpoint actions on the actual bar comma chains。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0292"></a>

### m0292 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarFrameSquares.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarFrameSquares.lean)|
|追加|2026-10-16T22:36:37+09:00 · `0babf6dcb65d`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFrameSquares.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFrameSquares.right_extension`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarFrameSquares.pair_extension`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Derived frame comparisons for the actual global bar cone squares。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0293"></a>

### m0293 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarReference.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarReference.lean)|
|追加|2026-10-16T21:02:18+09:00 · `5d02b7b07e52`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarReference.reference`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarReference.smallAction_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarReference.section_evaluation_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation on the actual identity-reference section of the resolution bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0294"></a>

### m0294 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarRowDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarRowDiagram.lean)|
|追加|2026-10-16T22:28:29+09:00 · `feb5b6e86d81`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowDiagram.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowDiagram.left_bar_recovery`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowDiagram.right_bar_recovery`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One strict diagram of the underlying row cone maps over all nerve simplices。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0295"></a>

### m0295 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarRowHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarRowHomotopy.lean)|
|追加|2026-10-16T22:09:27+09:00 · `465bb6792c0f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowHomotopy.sectionMap`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowHomotopy.right_isIso_iff_row`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowHomotopy.natural_right_isIso_iff_rows`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual bar homotopies from the reference to each row presentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0296"></a>

### m0296 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarRowOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarRowOperators.lean)|
|追加|2026-10-16T22:28:29+09:00 · `feb5b6e86d81`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowOperators.left`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowOperators.left_recovery`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowOperators.right_recovery`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All chain operator squares of the same strict row cone diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0297"></a>

### m0297 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarRowPresentations.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarRowPresentations.lean)|
|追加|2026-10-16T21:11:41+09:00 · `60697ddba22a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowPresentations.pair`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowPresentations.elementArrow`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowPresentations.elementArrow_underlying`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual resolution rows appear inside the existing framed bar。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0298"></a>

### m0298 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionBarSimplexCone.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionBarSimplexCone.lean)|
|追加|2026-10-16T22:18:00+09:00 · `8eed91979b75`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionBarSimplexCone.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarSimplexCone.elementArrow`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionBarSimplexCone.arrow_raw_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Each actual bar simplex maps to its exact evaluated row presentation。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0299"></a>

### m0299 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategory

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionCategory.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionCategory.lean)|
|追加|2026-10-16T07:52:11+09:00 · `fcbefc751616`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionObject`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.instFullProjection`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.diagram_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategoryHom](#m0300)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace](#m0311)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets](#m0084)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace](#m0085)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains](#m0091)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence](#m0103)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom](#m0110)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryMappingClassLabel](#m0250)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy](#m0252)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategoryHom](#m0300)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor](#m0303)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows](#m0304)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence](#m0307)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace](#m0311)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All cosimplicial resolutions over an arbitrary model category。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0300"></a>

### m0300 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCategoryHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionCategoryHom.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionCategoryHom.lean)|
|追加|2026-10-16T07:52:11+09:00 · `fcbefc751616`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.hom`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.piZeroEquiv_naturality_target`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.map_piZero_eq_of_base_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence](#m0307)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom](#m0110)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence](#m0307)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual mapping spaces on all resolutions and fibrant targets。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0301"></a>

### m0301 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionCenterRowLaws.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionCenterRowLaws.lean)|
|追加|2026-10-16T22:28:29+09:00 · `feb5b6e86d81`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLaws.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLaws.simplex`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLaws.component_id`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole-map restriction laws for actual center row lifts。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0302"></a>

### m0302 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLifts

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionCenterRowLifts.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionCenterRowLifts.lean)|
|追加|2026-10-16T22:18:00+09:00 · `8eed91979b75`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts.naturality`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLifts.transport`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Full row lifts from the same actual changing-center fiber diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0303"></a>

### m0303 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionFrameRowFunctor.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionFrameRowFunctor.lean)|
|追加|2026-10-16T21:11:41+09:00 · `60697ddba22a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRowFunctor.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRowFunctor.comparison`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRowFunctor.atDegree`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLifts](#m0302)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual row resolutions are functorial in framed comparison maps。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0304"></a>

### m0304 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionFrameRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionFrameRows.lean)|
|追加|2026-10-16T21:11:41+09:00 · `60697ddba22a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRows.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRows.augmentation_base`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRows.rowMap_base`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor](#m0303)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLaws](#m0301)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor](#m0303)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Every actual outer-frame row is a resolution of the original base。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0305"></a>

### m0305 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftAction.lean)|
|追加|2026-10-16T08:16:39+09:00 · `316d627d571f`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftAction.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftAction.rowComparison_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftAction.extends_action`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Resolution lift spaces act on the actual diagonal Hom。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0306"></a>

### m0306 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftFunctorLaws.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftFunctorLaws.lean)|
|追加|2026-10-16T09:54:18+09:00 · `0c8eb6c83508`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftFunctorLaws.pre_compose`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftFunctorLaws.interchange`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Exact unit, composition, and interchange laws for actual lift transports。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0307"></a>

### m0307 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftIndependence.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftIndependence.lean)|
|追加|2026-10-16T07:52:11+09:00 · `fcbefc751616`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionObject.hom_map_eq_of_base_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom](#m0110)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.LocalizedResolutionHom](#m0110)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Independence of resolution lifts in the homotopy category of spaces。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0308"></a>

### m0308 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftPostcomposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftPostcomposition.lean)|
|追加|2026-10-16T09:15:17+09:00 · `259e43beeb7e`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPostcomposition.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPostcomposition.raw_action`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPostcomposition.kan_action`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual postcomposition of higher resolution-lift families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0309"></a>

### m0309 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftPrecomposition.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftPrecomposition.lean)|
|追加|2026-10-16T09:23:34+09:00 · `9b98c444ee9c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPrecomposition.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPrecomposition.piZero_naturality_source`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftPrecomposition.kan_action`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace](#m0085)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameSquareComparison](#m0086)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor](#m0087)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization](#m0088)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains](#m0091)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionFunctors](#m0276)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Source change for higher resolution-lift families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0310"></a>

### m0310 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftRows.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftRows.lean)|
|追加|2026-10-16T22:18:00+09:00 · `8eed91979b75`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftRows.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftRows.parameter`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftRows.diagram_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLifts](#m0302)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual resolution maps carried by every higher lift simplex。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0311"></a>

### m0311 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftSpace

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionLiftSpace.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionLiftSpace.lean)|
|追加|2026-10-16T08:05:19+09:00 · `37ac8bddda2c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftSpace.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftSpace.kanComplex`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionLiftSpace.localizationIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FrameLiftSpace](#m0085)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory](#m0090)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftCoherence](#m0103)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRowFunctor](#m0303)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows](#m0304)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftAction](#m0305)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftFunctorLaws](#m0306)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftRows](#m0310)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Higher compatibility spaces for arbitrary resolution lifts。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0312"></a>

### m0312 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedActionOperators.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedActionOperators.lean)|
|追加|2026-10-16T17:51:14+09:00 · `5840161861db`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators.inputMap`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators.face_prefix`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedActionOperators.face_operator`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All external simplex operators on the same small mixed triangle and facet actions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0313"></a>

### m0313 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedBoundary.lean)|
|追加|2026-10-16T17:18:29+09:00 · `da71d1d985f6`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary.boundaryParameter`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary.shared_diagonal`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedBoundary.triangle_fit`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The two actual mixed triangle boundaries made from the same five whole edge systems。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0314"></a>

### m0314 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedCoherentDiagonal.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedCoherentDiagonal.lean)|
|追加|2026-10-16T17:13:03+09:00 · `e376cab5e1fa`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal.boundaryParameters`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal.coherent_one`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal.coherent_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The same selected mixed diagonal as one coherent family with both whole endpoints fixed。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0315"></a>

### m0315 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedCoherentTriangles.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedCoherentTriangles.lean)|
|追加|2026-10-16T17:26:25+09:00 · `1c295db1585c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles.coherent`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles.coherent_face`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles.shared_diagonal`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Retaining the old whole mixed triangles with their same whole facet and vertex systems。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0316"></a>

### m0316 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedDiagonalData.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedDiagonalData.lean)|
|追加|2026-10-16T17:13:03+09:00 · `e376cab5e1fa`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagonalData.arrowFunctor`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagonalData.fit`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagonalData.recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The already selected mixed diagonal fits the same whole endpoint and vertex boundary。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0317"></a>

### m0317 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedDiagram.lean)|
|追加|2026-10-16T16:41:53+09:00 · `17aa144d5fb0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagram.Presentation`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagram.vertexBoundary`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedDiagram.vertexInclusion_mono`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality](#m0324)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual all-center mixed squares and their commuting cubes。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0318"></a>

### m0318 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedEdgeRecovery.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedEdgeRecovery.lean)|
|追加|2026-10-16T16:41:53+09:00 · `17aa144d5fb0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery.preFamily`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery.intervalCD_face`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery.intervalBD_face`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The same four interval systems recover the four actual old mixed triangle boundary families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0319"></a>

### m0319 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedEndpointCompatibility.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedEndpointCompatibility.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility.point`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility.commonC`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility.commonD`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The same four interval systems share exactly the same whole corner systems。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0320"></a>

### m0320 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedFaceSystems.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedFaceSystems.lean)|
|追加|2026-10-16T17:13:03+09:00 · `e376cab5e1fa`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedFaceSystems.faces`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedFaceSystems.old_triangle_faces`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedFaceSystems.faces_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual five whole edge systems form the two compatible mixed triangle boundaries。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0321"></a>

### m0321 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedIntervalRestrictions.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedIntervalRestrictions.lean)|
|追加|2026-10-16T16:41:53+09:00 · `17aa144d5fb0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions.preAB`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions.castBD_evaluate`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions.intervalBD_evaluate`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual restrictions of the same selected interval system to mixed square edges。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0322"></a>

### m0322 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedRawEndpoints.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedRawEndpoints.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints.K`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints.BD_zero`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedRawEndpoints.BD_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Exact whole endpoints before the final mixed parameter and value transports。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0323"></a>

### m0323 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedReassociation.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedReassociation.lean)|
|追加|2026-10-16T16:41:53+09:00 · `17aa144d5fb0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociation.leftFinal`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociation.fiber_cast`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociation.bd_fibers`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality](#m0324)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality](#m0324)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual natural reassociation needed by the fourth selected interval。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0324"></a>

### m0324 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedReassociationEquality.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedReassociationEquality.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality.finalLeft_eq`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedReassociationEquality.toFinal_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Reassociation is equality transport of the same entire indexing functor。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0325"></a>

### m0325 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedSmallAction.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedSmallAction.lean)|
|追加|2026-10-16T17:42:17+09:00 · `c543585aa9ca`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallAction.input`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallAction.output_kanComplex`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallAction.point_action_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The whole coherent mixed triangles act on the original small resolution Hom spaces。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0326"></a>

### m0326 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedSmallFamilies.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedSmallFamilies.lean)|
|追加|2026-10-16T17:42:17+09:00 · `c543585aa9ca`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies.tuples`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies.family_face`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedSmallFamilies.shared_diagonal`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedActionOperators](#m0312)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Entire mixed triangle families in the original Hom universe on every external chain。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0327"></a>

### m0327 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedTriangleBoundary.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedTriangleBoundary.lean)|
|追加|2026-10-16T17:26:25+09:00 · `1c295db1585c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary.vertexParameter`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary.inclusion_mono`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary.triangle_fit`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The entire facet and vertex boundary of each original mixed triangle。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0328"></a>

### m0328 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedTriangles.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedTriangles.lean)|
|追加|2026-10-16T16:41:53+09:00 · `17aa144d5fb0`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangles.oldBoundary`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangles.face_recover`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedTriangles.diagonal_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The original whole mixed triangles and all their actual boundary families across centers。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0329"></a>

### m0329 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionMixedVertexRestrictions.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionMixedVertexRestrictions.lean)|
|追加|2026-10-16T17:26:25+09:00 · `1c295db1585c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions.V`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions.BD_vertices`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions.faces_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The same mixed interval systems fix the whole common vertex cylinder。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0330"></a>

### m0330 · HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping

|項目|記録|
|---|---|
|分類|B|
|ソース|[ResolutionRowMixedMapping.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/ResolutionRowMixedMapping.lean)|
|追加|2026-10-16T21:11:41+09:00 · `60697ddba22a`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.ResolutionRowMixedMapping.instModelCategoryFunctorSimplexCategory_serrePositivity`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionRowMixedMapping.rowComparison_weakEquivalence`<br>`SerrePositivity.HomotopyFunctionComplex.ResolutionRowMixedMapping.row_operator_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual resolution rows of the same mixed output, natural in all presentations。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0331"></a>

### m0331 · HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping

|項目|記録|
|---|---|
|分類|B|
|ソース|[RightResolutionMapping.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/RightResolutionMapping.lean)|
|追加|2026-10-16T19:51:40+09:00 · `1127bcd5cab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.RightResolutionMapping.Index`<br>`SerrePositivity.HomotopyFunctionComplex.RightResolutionMapping.kanComparison_piZero_bijective`<br>`SerrePositivity.HomotopyFunctionComplex.RightResolutionMapping.piZeroEquiv`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison](#m0060)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionInvariance](#m0126)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRows](#m0207)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows](#m0256)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Simultaneous source and target resolution mapping spaces。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0332"></a>

### m0332 · HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement

|項目|記録|
|---|---|
|分類|B|
|ソース|[RightResolutionRefinement.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/RightResolutionRefinement.lean)|
|追加|2026-10-16T19:51:40+09:00 · `1127bcd5cab4`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.RightResolutionRefinement.targetZero`<br>`SerrePositivity.HomotopyFunctionComplex.RightResolutionRefinement.kanRight`<br>`SerrePositivity.HomotopyFunctionComplex.RightResolutionRefinement.kanRight_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReplacementComparison](#m0213)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A natural weak span from existing presentations to target resolution mapping spaces。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0333"></a>

### m0333 · HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[SelectedIntervalDiagram.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SelectedIntervalDiagram.lean)|
|追加|2026-10-16T16:24:53+09:00 · `6a4960a942c1`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalDiagram.Presentation`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalDiagram.post_recover`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalDiagram.pre_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociation](#m0323)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One coherent system retaining all originally selected pre/post interval families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0334"></a>

### m0334 · HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints

|項目|記録|
|---|---|
|分類|B|
|ソース|[SelectedIntervalEndpoints.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SelectedIntervalEndpoints.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints.baseParameters`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints.reindexed_zero`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalEndpoints.reindexed_one`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Both entire endpoint systems of the same selected interval diagram。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0335"></a>

### m0335 · HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices

|項目|記録|
|---|---|
|分類|B|
|ソース|[SelectedIntervalVertices.lean](../SerrePositivity/HomotopicalAlgebra/HomotopyFunctionComplex/SelectedIntervalVertices.lean)|
|追加|2026-10-16T17:26:25+09:00 · `1c295db1585c`|
|主な公開宣言|`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices.vertices`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices.coherent_vertices`<br>`SerrePositivity.HomotopyFunctionComplex.SelectedIntervalVertices.reindexed_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The entire vertex cylinder remains fixed in the same selected interval system。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0336"></a>

### m0336 · HomotopicalAlgebra.Quillen.ContractibleParameters

|項目|記録|
|---|---|
|分類|A|
|ソース|[ContractibleParameters.lean](../SerrePositivity/HomotopicalAlgebra/Quillen/ContractibleParameters.lean)|
|追加|2026-10-16T20:49:38+09:00 · `52539e1eb0cc`|
|主な公開宣言|`SerrePositivity.Quillen.ContractibleParameters.graph_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.Quillen.ContractibleParameters.graph_weakEquivalence` — 可縮かつfibrantなパラメータを付加するグラフ射が弱同値となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0337"></a>

### m0337 · HomotopicalAlgebra.Replacement.FibrantCategory

|項目|記録|
|---|---|
|分類|A|
|ソース|[FibrantCategory.lean](../SerrePositivity/HomotopicalAlgebra/Replacement/FibrantCategory.lean)|
|追加|2026-10-16T18:26:10+09:00 · `41280dffcf32`|
|主な公開宣言|`SerrePositivity.ModelReplacement.FibrantReplacementObject.liftBase_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets](#m0084)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.Replacement.FibrantLocalization](#m0338)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DualResolutionTargets](#m0084)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison](#m0111)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingBifunctor](#m0273)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingDescent](#m0274)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionRefinement](#m0332)<br>[HomotopicalAlgebra.Replacement.FibrantLocalization](#m0338)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ModelReplacement.FibrantReplacementObject.liftBase_weakEquivalence` — fibrant置換の圏で基底の弱同値を持ち上げた比較射も弱同値となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0338"></a>

### m0338 · HomotopicalAlgebra.Replacement.FibrantLocalization

|項目|記録|
|---|---|
|分類|A|
|ソース|[FibrantLocalization.lean](../SerrePositivity/HomotopicalAlgebra/Replacement/FibrantLocalization.lean)|
|追加|2026-10-16T18:26:10+09:00 · `41280dffcf32`|
|主な公開宣言|`SerrePositivity.ModelReplacement.FibrantReplacementObject.localized_map_eq_of_base_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementMappingLocalization](#m0275)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.ModelReplacement.FibrantReplacementObject.localized_map_eq_of_base_eq` — 同じ基底射を覆うfibrant置換間の比較は局所化後に等しくなる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0339"></a>

### m0339 · HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest

|項目|記録|
|---|---|
|分類|B|
|ソース|[AnchoredChainFiniteTest.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnchoredChainFiniteTest.lean)|
|追加|2026-10-16T18:12:55+09:00 · `6bfedb29b930`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.stableIso`<br>`SerrePositivity.SimplicialModel.AnchoredChainFiniteTest.test_operator`<br>`SerrePositivity.SimplicialModel.AnchoredChainFiniteTest.test_reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallFamilies](#m0058)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole finite test parameters of the actual large factorization-chain space。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0340"></a>

### m0340 · HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneHomotopyLocalization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneHomotopyLocalization.lean)|
|追加|2026-10-16T19:20:01+09:00 · `42d73f5277b5`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneHomotopy.map_homotopy_eq`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)<br>[HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor](#m0343)<br>[HomotopicalAlgebra.Simplicial.AnodyneModelDetection](#m0344)<br>[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)<br>[HomotopicalAlgebra.Simplicial.HomotopyClasses](#m0402)<br>[HomotopicalAlgebra.Simplicial.KanPostDetection](#m0427)<br>[HomotopicalAlgebra.Simplicial.NerveInitialImage](#m0474)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison](#m0519)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)<br>[HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex](#m0572)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)<br>[HomotopicalAlgebra.Simplicial.WordSegmentComparison](#m0618)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarBaseInvariance](#m0135)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation](#m0158)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor](#m0343)<br>[HomotopicalAlgebra.Simplicial.AnodyneModelDetection](#m0344)<br>[HomotopicalAlgebra.Simplicial.AnodyneNonempty](#m0345)<br>[HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization](#m0356)<br>[HomotopicalAlgebra.Simplicial.BoundaryRightColimit](#m0357)<br>[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)<br>[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)<br>[HomotopicalAlgebra.Simplicial.HomotopyClasses](#m0402)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts](#m0417)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite](#m0421)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension](#m0424)<br>[HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy](#m0425)<br>[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)<br>[HomotopicalAlgebra.Simplicial.KanPostDetection](#m0427)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)<br>[HomotopicalAlgebra.Simplicial.KanPushoutComparison](#m0429)<br>[HomotopicalAlgebra.Simplicial.KanPushoutCube](#m0430)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)<br>[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)<br>[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)<br>[HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization](#m0451)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction](#m0452)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)<br>[HomotopicalAlgebra.Simplicial.NerveInitialImage](#m0474)<br>[HomotopicalAlgebra.Simplicial.OppositeHomotopy](#m0506)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison](#m0519)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation](#m0546)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)<br>[HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex](#m0572)<br>[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)<br>[HomotopicalAlgebra.Simplicial.SplitLocalizedDescent](#m0578)<br>[HomotopicalAlgebra.Simplicial.UnderMonoBrown](#m0587)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne](#m0588)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)<br>[HomotopicalAlgebra.Simplicial.WordSegmentComparison](#m0618)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneHomotopy.map_homotopy_eq` — anodyne射を反転する関手は単体的にホモトピックな二射を同じ射へ送る。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0341"></a>

### m0341 · HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneIntervalEndpoints.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneIntervalEndpoints.lean)|
|追加|2026-10-16T19:20:01+09:00 · `42d73f5277b5`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneHomotopy.endpoint_zero_anodyne`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization](#m0340)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization](#m0340)<br>[HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension](#m0411)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension](#m0422)<br>[HomotopicalAlgebra.Simplicial.WordSegmentComparison](#m0618)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneHomotopy.endpoint_zero_anodyne` — 単体的な区間の始点の包含はモデル構造を仮定せずanodyneである。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0342"></a>

### m0342 · HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneKanReplacement.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean)|
|追加|2026-10-16T23:58:11+09:00 · `15e2b83931ba`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneKanReplacement.terminal_rlp`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneKanReplacement.terminal_rlp` — hornの小対象論法で作った置換の値が全hornに対する右持ち上げ性を持つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0343"></a>

### m0343 · HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneLocalizedTensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneLocalizedTensor.lean)|
|追加|2026-10-16T23:58:11+09:00 · `15e2b83931ba`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneHomotopy.whiskerLeft_anodyneQ_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.SplitLocalizedDescent](#m0578)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.SplitLocalizedDescent](#m0578)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneHomotopy.whiskerLeft_anodyneQ_isIso` — anodyne局所化で可逆な射に左から直積を取っても局所化で可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0344"></a>

### m0344 · HomotopicalAlgebra.Simplicial.AnodyneModelDetection

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneModelDetection.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneModelDetection.lean)|
|追加|2026-10-16T19:20:01+09:00 · `42d73f5277b5`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneHomotopy.weakEquivalences_iff_anodyneQ_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne](#m0588)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne](#m0588)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneHomotopy.weakEquivalences_iff_anodyneQ_isIso` — 指定した小さい単体モデルの弱同値はanodyne局所化で可逆な射と一致する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0345"></a>

### m0345 · HomotopicalAlgebra.Simplicial.AnodyneNonempty

|項目|記録|
|---|---|
|分類|A|
|ソース|[AnodyneNonempty.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/AnodyneNonempty.lean)|
|追加|2026-10-17T02:13:59+09:00 · `3fc5c6030758`|
|主な公開宣言|`SerrePositivity.SimplicialModel.AnodyneNonempty.nonempty_iff_of_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.AnodyneNonempty.nonempty_iff_of_localized_isIso` — anodyne局所化で可逆な射は頂点の非空性を両方向に保存する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0346"></a>

### m0346 · HomotopicalAlgebra.Simplicial.BarAugmentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[BarAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BarAugmentation.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.augmentation`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.augmentation` — 図式の指定した余錐から実際のbar構成のaugmentationを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0347"></a>

### m0347 · HomotopicalAlgebra.Simplicial.BarConstruction

|項目|記録|
|---|---|
|分類|A|
|ソース|[BarConstruction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BarConstruction.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.functor`<br>`SerrePositivity.SimplicialModel.BarConstruction.rows`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.BarAugmentation](#m0346)<br>[HomotopicalAlgebra.Simplicial.BarSize](#m0348)<br>[HomotopicalAlgebra.Simplicial.RelativeBarConstruction](#m0522)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BarAugmentation](#m0346)<br>[HomotopicalAlgebra.Simplicial.BarSize](#m0348)<br>[HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation](#m0521)<br>[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.functor` — 添字と値の宇宙を分けたモデル構造不要のbar関手を構成する。|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.rows` — 図式の各次数の要素の圏のnerveから二重単体的なbarの行を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0348"></a>

### m0348 · HomotopicalAlgebra.Simplicial.BarSize

|項目|記録|
|---|---|
|分類|B|
|ソース|[BarSize.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BarSize.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.pointDiagram`<br>`SerrePositivity.SimplicialModel.BarConstruction.index_small_of_bar_zero_small`<br>`SerrePositivity.SimplicialModel.BarConstruction.point_bar_not_small`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Raw bar size can grow even for a diagram of points。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0349"></a>

### m0349 · HomotopicalAlgebra.Simplicial.BinaryCotensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[BinaryCotensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BinaryCotensor.lean)|
|追加|2026-10-16T16:06:38+09:00 · `da59b69519b7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BinaryCotensor.glue`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BinaryCotensor.glue` — 二つの余テンソル族を実際の二項余積上に貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0350"></a>

### m0350 · HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles

|項目|記録|
|---|---|
|分類|B|
|ソース|[BinaryIntervalTriangles.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BinaryIntervalTriangles.lean)|
|追加|2026-10-17T10:25:56+09:00 · `5309c7668c57`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BinaryIntervalTriangles.firstFixed`<br>`SerrePositivity.SimplicialModel.BinaryIntervalTriangles.lower_comparison`<br>`SerrePositivity.SimplicialModel.BinaryIntervalTriangles.upper_comparison`|
|直接import元|[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The two actual triangles in a binary homotopy square。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0351"></a>

### m0351 · HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy

|項目|記録|
|---|---|
|分類|A|
|ソース|[BisimplicialCofibrancy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BisimplicialCofibrancy.lean)|
|追加|2026-10-16T08:26:05+09:00 · `27b29cedd054`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.isCofibrant`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization](#m0356)<br>[HomotopicalAlgebra.Simplicial.DiagonalCofibrations](#m0382)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization](#m0356)<br>[HomotopicalAlgebra.Simplicial.DiagonalCofibrations](#m0382)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.isCofibrant` — 標準的な単射cofibration条件のもとで二重単体的集合はReedy cofibrantである。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0352"></a>

### m0352 · HomotopicalAlgebra.Simplicial.BoundaryCotensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryCotensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryCotensor.lean)|
|追加|2026-10-16T14:46:40+09:00 · `79fe1764d240`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryCotensor.standardDesc`|
|直接import元|[HomotopicalAlgebra.Simplicial.BinaryCotensor](#m0349)<br>[HomotopicalAlgebra.Simplicial.BoundaryTensorGluing](#m0358)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornOverlap](#m0378)<br>[HomotopicalAlgebra.Simplicial.NaturalHornFilling](#m0455)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor](#m0515)<br>[HomotopicalAlgebra.Simplicial.PushoutCotensor](#m0516)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BinaryCotensor](#m0349)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornOverlap](#m0378)<br>[HomotopicalAlgebra.Simplicial.NaturalHornFilling](#m0455)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor](#m0515)<br>[HomotopicalAlgebra.Simplicial.PushoutCotensor](#m0516)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryCotensor.standardDesc` — 互換な余テンソルの面の全族を単体境界上に貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0353"></a>

### m0353 · HomotopicalAlgebra.Simplicial.BoundaryFillerLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryFillerLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryFillerLifting.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryFillerLifting.terminal_rightLifting`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryFillerLifting.terminal_rightLifting` — 全次元の境界充填からすべての単射に対する右持ち上げ性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0354"></a>

### m0354 · HomotopicalAlgebra.Simplicial.BoundaryGluing

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryGluing.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryGluing.lean)|
|追加|2026-10-16T09:42:54+09:00 · `1ff62113d16f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryGluing.standardDesc`<br>`SerrePositivity.SimplicialModel.BoundaryGluing.standardDesc_fac`|
|直接import元|[HomotopicalAlgebra.Simplicial.BoundaryCotensor](#m0352)<br>[HomotopicalAlgebra.Simplicial.LargeParameterMapping](#m0443)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary](#m0535)<br>[HomotopicalAlgebra.Simplicial.SkeletalCellGluing](#m0569)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.Simplicial.BoundaryCotensor](#m0352)<br>[HomotopicalAlgebra.Simplicial.BoundaryTensorGluing](#m0358)<br>[HomotopicalAlgebra.Simplicial.LargeParameterMapping](#m0443)<br>[HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor](#m0515)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary](#m0535)<br>[HomotopicalAlgebra.Simplicial.SelectedTriangle](#m0553)<br>[HomotopicalAlgebra.Simplicial.SkeletalCellGluing](#m0569)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryGluing.standardDesc` — 互換な標準面の族を実際の単体境界上の一つの射に貼り合わせる。|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryGluing.standardDesc_fac` — 境界へ貼り合わせた射の各標準面への制限は指定した面そのものとなる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0355"></a>

### m0355 · HomotopicalAlgebra.Simplicial.BoundaryOneCotensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryOneCotensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryOneCotensor.lean)|
|追加|2026-10-16T14:40:20+09:00 · `78b8b659ef20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryOneCotensor.glue`|
|直接import元|[HomotopicalAlgebra.Simplicial.BinaryCotensor](#m0349)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryOneCotensor.glue` — 区間境界の二つの頂点に指定した余テンソル族を貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0356"></a>

### m0356 · HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryReedyFactorization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryReedyFactorization.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.BoundaryFactorization.reedy_wfs`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.BoundaryFactorization.reedy_wfs` — 境界の左右持ち上げクラスからモデル構造不要のReedy弱因子分解系を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0357"></a>

### m0357 · HomotopicalAlgebra.Simplicial.BoundaryRightColimit

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryRightColimit.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryRightColimit.lean)|
|追加|2026-10-17T01:13:22+09:00 · `1fe081476cdf`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryRightColimit.filtered_rlp`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryRightColimit.filtered_rlp` — 境界に対する右持ち上げ性がfilteredな余極限で保たれる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0358"></a>

### m0358 · HomotopicalAlgebra.Simplicial.BoundaryTensorGluing

|項目|記録|
|---|---|
|分類|A|
|ソース|[BoundaryTensorGluing.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/BoundaryTensorGluing.lean)|
|追加|2026-10-17T05:45:53+09:00 · `ca74aeaecee2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BoundaryTensorGluing.desc`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.Simplicial.RelativeProductLifting](#m0544)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryExt](#m0138)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceBoundaryGluing](#m0139)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceTriangleGluing](#m0145)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling](#m0534)<br>[HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle](#m0542)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BoundaryTensorGluing.desc` — 互換なテンソル付きの全面の族を単体境界全体に貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0359"></a>

### m0359 · HomotopicalAlgebra.Simplicial.CellularNaturalComparison

|項目|記録|
|---|---|
|分類|A|
|ソース|[CellularNaturalComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CellularNaturalComparison.lean)|
|追加|2026-10-17T01:20:19+09:00 · `bb54cd3df030`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CellularNaturalComparison.app_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.CellularNaturalComparison.app_isIso` — 余連続で単射を保つ関手間の自然比較の可逆性を標準単体上の可逆性から導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0360"></a>

### m0360 · HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition

|項目|記録|
|---|---|
|分類|A|
|ソース|[ClosedHomotopyComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ClosedHomotopyComposition.lean)|
|追加|2026-10-17T09:43:15+09:00 · `a5cdb28eea6b`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ClosedHomotopyComposition.comp_naturality`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ClosedHomotopyComposition.comp_naturality` — 閉構造による区間写像の合成はパラメータの変更と整合する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0361"></a>

### m0361 · HomotopicalAlgebra.Simplicial.ClosedParameterComposition

|項目|記録|
|---|---|
|分類|A|
|ソース|[ClosedParameterComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ClosedParameterComposition.lean)|
|追加|2026-10-17T08:11:58+09:00 · `933d84903b7c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ClosedParameterComposition.curry_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ClosedParameterComposition.curry_comp` — 共有パラメータを持つ射の合成の転置は内部Homの標準合成に一致する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0362"></a>

### m0362 · HomotopicalAlgebra.Simplicial.ClosedParameterUnits

|項目|記録|
|---|---|
|分類|A|
|ソース|[ClosedParameterUnits.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ClosedParameterUnits.lean)|
|追加|2026-10-17T10:25:56+09:00 · `5309c7668c57`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ClosedParameterUnits.identity_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ClosedParameterUnits.identity_comp` — 共有パラメータ上の内部Homの左単位則が実写像の等式として成り立つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0363"></a>

### m0363 · HomotopicalAlgebra.Simplicial.CodiscreteNerveExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[CodiscreteNerveExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CodiscreteNerveExtension.lean)|
|追加|2026-10-17T02:13:59+09:00 · `3fc5c6030758`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CodiscreteNerveExtension.kanComplex`|
|直接import元|[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)<br>[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.CodiscreteNerveExtension.kanComplex` — 点を持つcodiscrete圏のnerveは全hornを充填できるKan複体である。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0364"></a>

### m0364 · HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonCoherenceRestriction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonCoherenceRestriction.lean)|
|追加|2026-10-17T10:20:18+09:00 · `6f4db4b0b505`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonCoherenceRestriction.triangle`<br>`SerrePositivity.SimplicialModel.ComparisonCoherenceRestriction.left_tetrahedron_comp`<br>`SerrePositivity.SimplicialModel.ComparisonCoherenceRestriction.right_tetrahedron_comp`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Parameter restriction of entire selected tetrahedra and comparison discs。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0365"></a>

### m0365 · HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonCoherenceTransport.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonCoherenceTransport.lean)|
|追加|2026-10-17T10:20:18+09:00 · `6f4db4b0b505`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonCoherenceTransport.tetrahedron`<br>`SerrePositivity.SimplicialModel.ComparisonCoherenceTransport.square_left_triangle`<br>`SerrePositivity.SimplicialModel.ComparisonCoherenceTransport.square_right_triangle`|
|直接import元|[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transport selected comparison tetrahedra and a whole comparison disc。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0366"></a>

### m0366 · HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleBinary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleBinary.lean)|
|追加|2026-10-17T10:10:39+09:00 · `cf862ed3c08f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonTriangleBinary.rightFamily`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleBinary.changeEdges`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleBinary.changeEdges_comparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Compose a specified triangle with a specified interval。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0367"></a>

### m0367 · HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleChoices.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleChoices.lean)|
|追加|2026-10-17T09:49:11+09:00 · `646b0cb95d2d`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonTriangleChoices.obj`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleChoices.relative_extension`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleChoices.fixedBoundaryComparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The small space of all comparison triangles with both chosen edges fixed。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0368"></a>

### m0368 · HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleDegeneracy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleDegeneracy.lean)|
|追加|2026-10-17T10:25:56+09:00 · `5309c7668c57`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonTriangleDegeneracy.face_collapse_zero`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleDegeneracy.family_second`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleDegeneracy.family_constant`|
|直接import元|[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Degenerate comparison triangles and a fixed-edge round-trip coherence。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0369"></a>

### m0369 · HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleHorn.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleHorn.lean)|
|追加|2026-10-17T09:49:11+09:00 · `646b0cb95d2d`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanComparisonTriangle.hornFaces`<br>`SerrePositivity.SimplicialModel.KanComparisonTriangle.hornMap_one`<br>`SerrePositivity.SimplicialModel.KanComparisonTriangle.Data.horn_restriction`|
|直接import元|[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron](#m0408)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The specified two comparison edges glue to their actual outer horn。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0370"></a>

### m0370 · HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleParameterDiagram.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleParameterDiagram.lean)|
|追加|2026-10-17T10:03:40+09:00 · `e455b341e062`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonTriangleParameterDiagram.diagram`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleParameterDiagram.pointInterval_zero`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleParameterDiagram.pointInterval_one`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict small parameter diagram with natural families of comparison triangles。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0371"></a>

### m0371 · HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[ComparisonTriangleTransport.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ComparisonTriangleTransport.lean)|
|追加|2026-10-17T09:54:58+09:00 · `b18f89d69395`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ComparisonTriangleTransport.hornMap_post`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleTransport.map_id`<br>`SerrePositivity.SimplicialModel.ComparisonTriangleTransport.map_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Strict transport of whole comparison triangle spaces along maps of their two edges。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0372"></a>

### m0372 · HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation

|項目|記録|
|---|---|
|分類|B|
|ソース|[CompatibleHornFillingOperation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CompatibleHornFillingOperation.lean)|
|追加|2026-10-17T10:50:31+09:00 · `401c6fd21a3d`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CompatibleHornFillingOperation.inputs`<br>`SerrePositivity.SimplicialModel.CompatibleHornFillingOperation.fill_prescribed`<br>`SerrePositivity.SimplicialModel.CompatibleHornFillingOperation.family_prescribed`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One filling operation retains arbitrarily many compatible prescribed families。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0373"></a>

### m0373 · HomotopicalAlgebra.Simplicial.CompatibleInputMap

|項目|記録|
|---|---|
|分類|C|
|ソース|[CompatibleInputMap.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CompatibleInputMap.lean)|
|追加|2026-10-17T11:23:20+09:00 · `8f460a197d13`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CompatibleInputMap.map`<br>`SerrePositivity.SimplicialModel.CompatibleInputMap.map_inclusion`<br>`SerrePositivity.SimplicialModel.CompatibleInputMap.toInputs_map`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|一般の入力像の写像にも見えるが、充填入力APIとの結合が強く、独立した再利用契約が未確定。|
|現状の構成|A map of input families induces a map on their small unions。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0374"></a>

### m0374 · HomotopicalAlgebra.Simplicial.CompatibleInputUnion

|項目|記録|
|---|---|
|分類|C|
|ソース|[CompatibleInputUnion.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CompatibleInputUnion.lean)|
|追加|2026-10-17T10:50:31+09:00 · `401c6fd21a3d`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CompatibleInputUnion.Compatible`<br>`SerrePositivity.SimplicialModel.CompatibleInputUnion.toInputs_lift`<br>`SerrePositivity.SimplicialModel.CompatibleInputUnion.lift_over`|
|直接import元|[HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation](#m0372)<br>[HomotopicalAlgebra.Simplicial.CompatibleInputMap](#m0373)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation](#m0372)<br>[HomotopicalAlgebra.Simplicial.CompatibleInputMap](#m0373)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|入力像の和は一般的だが、相対充填の互換性を前提にしており、独立した用途が未確定。|
|現状の構成|Glue compatible input prescriptions, with arbitrarily large index type。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0375"></a>

### m0375 · HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn

|項目|記録|
|---|---|
|分類|C|
|ソース|[CosimplicialDegenerateHorn.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CosimplicialDegenerateHorn.lean)|
|追加|2026-10-17T11:00:32+09:00 · `7ed4a33f06d6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CosimplicialDegenerateHorn.eq_of_faces`|
|直接import元|[HomotopicalAlgebra.Simplicial.DegenerateHornOverlap](#m0378)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DegenerateHornOverlap](#m0378)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|圏論的な形は一般的だが、現状の利用は正規化hornの退化入力に限定される。|
|現状の構成|Degenerate maps with the same horn agree for any cosimplicial object。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0376"></a>

### m0376 · HomotopicalAlgebra.Simplicial.CurriedHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[CurriedHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/CurriedHomotopy.lean)|
|追加|2026-10-17T00:20:33+09:00 · `def378c3c827`|
|主な公開宣言|`SerrePositivity.SimplicialModel.CurriedHomotopy.ofEdge`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)<br>[HomotopicalAlgebra.Simplicial.PrecompositionHomotopy](#m0514)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.CurriedHomotopy.ofEdge` — 写像単体的集合の指定した辺から元の全区間ホモトピーを構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0377"></a>

### m0377 · HomotopicalAlgebra.Simplicial.DegenerateHornInput

|項目|記録|
|---|---|
|分類|B|
|ソース|[DegenerateHornInput.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DegenerateHornInput.lean)|
|追加|2026-10-17T10:44:23+09:00 · `64adc4f99794`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DegenerateHornInput.visibleFace`<br>`SerrePositivity.SimplicialModel.DegenerateHornInput.section_degeneracy`<br>`SerrePositivity.SimplicialModel.DegenerateHornInput.family_degeneracy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn](#m0375)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)<br>[HomotopicalAlgebra.Simplicial.NaturalHornFilling](#m0455)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn](#m0375)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornOverlap](#m0378)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)<br>[HomotopicalAlgebra.Simplicial.NaturalHornFilling](#m0455)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Degenerate horn inputs embed and admit a normalized filling operation。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0378"></a>

### m0378 · HomotopicalAlgebra.Simplicial.DegenerateHornOverlap

|項目|記録|
|---|---|
|分類|B|
|ソース|[DegenerateHornOverlap.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DegenerateHornOverlap.lean)|
|追加|2026-10-17T11:00:32+09:00 · `7ed4a33f06d6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DegenerateHornOverlap.eq_of_same_horn`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Any two degenerate whole horn families agree on their overlap。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0379"></a>

### m0379 · HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap

|項目|記録|
|---|---|
|分類|B|
|ソース|[DegenerateTriangleOverlap.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DegenerateTriangleOverlap.lean)|
|追加|2026-10-17T10:52:25+09:00 · `880c661b5d70`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DegenerateTriangleOverlap.interval`<br>`SerrePositivity.SimplicialModel.DegenerateTriangleOverlap.constant`<br>`SerrePositivity.SimplicialModel.DegenerateTriangleOverlap.eq_of_same_horn`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Two degenerate triangles with the same horn are the same whole triangle。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0380"></a>

### m0380 · HomotopicalAlgebra.Simplicial.DiagonalAdjunction

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalAdjunction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalAdjunction.lean)|
|追加|2026-10-16T08:26:05+09:00 · `27b29cedd054`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.diagonalAdjunction`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.BarConstruction](#m0347)<br>[HomotopicalAlgebra.Simplicial.DiagonalCofibrations](#m0382)<br>[HomotopicalAlgebra.Simplicial.DiagonalRepresentables](#m0389)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows](#m0121)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping](#m0330)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.Simplicial.BarConstruction](#m0347)<br>[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.DiagonalCofibrations](#m0382)<br>[HomotopicalAlgebra.Simplicial.DiagonalInternalHom](#m0383)<br>[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)<br>[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)<br>[HomotopicalAlgebra.Simplicial.DiagonalRepresentables](#m0389)<br>[HomotopicalAlgebra.Simplicial.RelativeBarConstruction](#m0522)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonalAdjunction` — 二重単体的集合の対角関手と実際の右随伴の随伴を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0381"></a>

### m0381 · HomotopicalAlgebra.Simplicial.DiagonalAnodyne

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalAnodyne.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalAnodyne.lean)|
|追加|2026-10-17T08:46:44+09:00 · `b801be5f0983`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.diagonal_map_anodyne`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonal_map_anodyne` — 二重単体的集合の対角はReedy anodyne射をanodyne射へ送る。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0382"></a>

### m0382 · HomotopicalAlgebra.Simplicial.DiagonalCofibrations

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalCofibrations.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalCofibrations.lean)|
|追加|2026-10-16T08:26:05+09:00 · `27b29cedd054`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.diagonal_map_mono`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonal_map_mono` — 二重単体的集合のReedy cofibrationの対角は単射となる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0383"></a>

### m0383 · HomotopicalAlgebra.Simplicial.DiagonalInternalHom

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalInternalHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalInternalHom.lean)|
|追加|2026-10-16T08:35:21+09:00 · `5fbc9855acfd`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.diagonalInternalHomAdjunction`<br>`SerrePositivity.BisimplicialModel.rightAdjointInternalHomIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalMatching](#m0386)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.DiagonalMatching](#m0386)<br>[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)<br>[HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching](#m0388)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonalInternalHomAdjunction` — 対角の右随伴を標準単体の内部Homで表す随伴を構成する。|
|入口の主張|`SerrePositivity.BisimplicialModel.rightAdjointInternalHomIso` — 対角の右随伴を各行の内部Homで表す自然同型を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0384"></a>

### m0384 · HomotopicalAlgebra.Simplicial.DiagonalKanTests

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalKanTests.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalKanTests.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.localized_diagonal_map_of_reedy_localizedMonos`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.localized_diagonal_map_of_reedy_localizedMonos` — Reedy局所化単射の対角がanodyne局所化で可逆となることをKan値テストから導く。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0385"></a>

### m0385 · HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalLocalizedEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalLocalizedEquivalence.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.localized_diagonal_map`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence](#m0241)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.localized_diagonal_map` — 各行で局所化可逆な二重単体写像の対角は局所化可逆となる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0386"></a>

### m0386 · HomotopicalAlgebra.Simplicial.DiagonalMatching

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalMatching.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalMatching.lean)|
|追加|2026-10-16T08:48:38+09:00 · `5f020cfcb181`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.matchingBoundaryIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching](#m0388)<br>[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching](#m0388)<br>[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.matchingBoundaryIso` — 対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0387"></a>

### m0387 · HomotopicalAlgebra.Simplicial.DiagonalQuillen

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalQuillen.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalQuillen.lean)|
|追加|2026-10-16T08:48:38+09:00 · `5f020cfcb181`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.diagonal_map_weakEquivalence`<br>`SerrePositivity.BisimplicialModel.diagonal_isLeftQuillen`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRawMapping](#m0061)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightMapping](#m0063)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalMappingWeakEquivalence](#m0083)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalRows](#m0121)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonal_map_weakEquivalence` — 各行が弱同値である二重単体写像の対角も弱同値となる。|
|入口の主張|`SerrePositivity.BisimplicialModel.diagonal_isLeftQuillen` — 指定した単体モデルとReedyモデルのもとで対角関手が左Quillen関手となる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0388"></a>

### m0388 · HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalRelativeMatching.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalRelativeMatching.lean)|
|追加|2026-10-16T08:48:38+09:00 · `5f020cfcb181`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.relativeMatchingArrowIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalAnodyne](#m0381)<br>[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.DiagonalQuillen](#m0387)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.relativeMatchingArrowIso` — 対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0389"></a>

### m0389 · HomotopicalAlgebra.Simplicial.DiagonalRepresentables

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiagonalRepresentables.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagonalRepresentables.lean)|
|追加|2026-10-16T08:35:21+09:00 · `5fbc9855acfd`|
|主な公開宣言|`SerrePositivity.BisimplicialModel.rightAdjointValueEquiv`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.DiagonalInternalHom](#m0383)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalInternalHom](#m0383)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.BisimplicialModel.rightAdjointValueEquiv` — 対角の右随伴の各値を制限された表現可能関手からの写像として表す。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0390"></a>

### m0390 · HomotopicalAlgebra.Simplicial.DiagramQuotient

|項目|記録|
|---|---|
|分類|C|
|ソース|[DiagramQuotient.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiagramQuotient.lean)|
|追加|2026-10-17T02:25:25+09:00 · `a9ec45e7bd04`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiagramQuotient.Congruence`<br>`SerrePositivity.SimplicialModel.DiagramQuotient.kernelComparison_isIso`<br>`SerrePositivity.SimplicialModel.DiagramQuotient.kernel_small`|
|直接import元|[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)<br>[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|安定合同による商は一般的だが、図式の小値化と切り離した境界が未確定。|
|現状の構成|Quotients of entire simplicial diagrams by stable degreewise congruences。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0391"></a>

### m0391 · HomotopicalAlgebra.Simplicial.DiscreteFamily

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiscreteFamily.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiscreteFamily.lean)|
|追加|2026-10-17T04:42:45+09:00 · `e2e5f576c0d8`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiscreteFamily.fiberIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.DiscreteFamily.fiberIso` — 離散ラベルで添字付けた直和の各ファイバーを元の単体的集合と同型で結ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0392"></a>

### m0392 · HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiscreteFamilyLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiscreteFamilyLifting.lean)|
|追加|2026-10-17T04:42:45+09:00 · `e2e5f576c0d8`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiscreteFamily.projection_mono_rlp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.DiscreteFamily.projection_mono_rlp` — 各離散ファイバーのすべての単射に対する右持ち上げ性から全体の射影の右持ち上げ性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0393"></a>

### m0393 · HomotopicalAlgebra.Simplicial.DiscreteFiber

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiscreteFiber.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiscreteFiber.lean)|
|追加|2026-10-17T04:42:45+09:00 · `e2e5f576c0d8`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiscreteFiber.map`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiscreteFamily](#m0391)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiscreteFamily](#m0391)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.DiscreteFiber.map` — 離散ラベルを保つ写像から実際の単体的ファイバー間の写像を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0394"></a>

### m0394 · HomotopicalAlgebra.Simplicial.DiscreteKanExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiscreteKanExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiscreteKanExtension.lean)|
|追加|2026-10-17T03:11:25+09:00 · `41f5c16cf8d9`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiscreteKanExtension.naturalExtension`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.DiscreteKanExtension.naturalExtension` — 離散値の写像をKan置換に沿って一意かつ自然に延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0395"></a>

### m0395 · HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[DiscreteLocalizedExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/DiscreteLocalizedExtension.lean)|
|追加|2026-10-17T03:16:09+09:00 · `5adb629cbaca`|
|主な公開宣言|`SerrePositivity.SimplicialModel.DiscreteLocalizedExtension.descend`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.DiscreteLocalizedExtension.descend` — 離散値の自然変換を局所化で可逆な射に沿って一意に降下させる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0396"></a>

### m0396 · HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[ExtraDegeneracyContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ExtraDegeneracyContraction.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.localized_augmentation_isIso`<br>`SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.contraction`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.Simplicial.OppositeHomotopy](#m0506)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.Simplicial.OppositeHomotopy](#m0506)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.localized_augmentation_isIso` — 追加退化を持つaugmentationはanodyne局所化で可逆となる。|
|入口の主張|`SerrePositivity.SimplicialModel.ExtraDegeneracyContraction.contraction` — 追加退化から実際の区間ホモトピーによる収縮を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0397"></a>

### m0397 · HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval

|項目|記録|
|---|---|
|分類|A|
|ソース|[ExtraDegeneracyInterval.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ExtraDegeneracyInterval.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ExtraDegeneracyInterval.intervalMap`|
|直接import元|[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction](#m0396)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ExtraDegeneracyInterval.intervalMap` — 追加退化から実際の標準区間シリンダー上の写像を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0398"></a>

### m0398 · HomotopicalAlgebra.Simplicial.FiberFunctor

|項目|記録|
|---|---|
|分類|A|
|ソース|[FiberFunctor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/FiberFunctor.lean)|
|追加|2026-10-16T13:27:39+09:00 · `7c8e969c76b7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.FiberFunctor.liftFamily`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.Simplicial.FiberFunctorReindex](#m0399)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.Simplicial.FiberFunctorReindex](#m0399)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.FiberFunctor.liftFamily` — 図式内の実際のpullbackファイバーへ整合する族を持ち上げる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0399"></a>

### m0399 · HomotopicalAlgebra.Simplicial.FiberFunctorReindex

|項目|記録|
|---|---|
|分類|A|
|ソース|[FiberFunctorReindex.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/FiberFunctorReindex.lean)|
|追加|2026-10-16T15:09:35+09:00 · `673dd59a1084`|
|主な公開宣言|`SerrePositivity.SimplicialModel.FiberFunctor.reindex`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.FiberFunctor.reindex` — 実際のファイバー図式を添字関手に沿って制限する比較を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0400"></a>

### m0400 · HomotopicalAlgebra.Simplicial.FreeWordHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[FreeWordHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/FreeWordHom.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.SimplicialModel.FreeWordHom.degreeEquiv`<br>`SerrePositivity.SimplicialModel.FreeWordHom.augmentation_app`<br>`SerrePositivity.SimplicialModel.FreeWordHom.localized_augmentation_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual ambient-word Hom augmentation for a free source is inverted。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0401"></a>

### m0401 · HomotopicalAlgebra.Simplicial.HomotopyBinarySquare

|項目|記録|
|---|---|
|分類|A|
|ソース|[HomotopyBinarySquare.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/HomotopyBinarySquare.lean)|
|追加|2026-10-17T09:43:15+09:00 · `a5cdb28eea6b`|
|主な公開宣言|`SerrePositivity.SimplicialModel.HomotopyBinarySquare.simultaneous_naturality`|
|直接import元|[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary](#m0366)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary](#m0366)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.HomotopyBinarySquare.simultaneous_naturality` — 二つの区間を二項演算で同時に合成した族はパラメータ変更に自然である。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0402"></a>

### m0402 · HomotopicalAlgebra.Simplicial.HomotopyClasses

|項目|記録|
|---|---|
|分類|A|
|ソース|[HomotopyClasses.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/HomotopyClasses.lean)|
|追加|2026-10-16T19:38:32+09:00 · `472439f68f78`|
|主な公開宣言|`SerrePositivity.SimplicialModel.HomotopyClasses.map_isIso_of_tests`|
|直接import元|[HomotopicalAlgebra.Simplicial.HomotopyBinarySquare](#m0401)<br>[HomotopicalAlgebra.Simplicial.HomotopyClassesClosed](#m0403)<br>[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyExtension](#m0414)<br>[HomotopicalAlgebra.Simplicial.PrecompositionHomotopy](#m0514)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.Simplicial.AnodyneNonempty](#m0345)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)<br>[HomotopicalAlgebra.Simplicial.HomotopyBinarySquare](#m0401)<br>[HomotopicalAlgebra.Simplicial.HomotopyClassesClosed](#m0403)<br>[HomotopicalAlgebra.Simplicial.HomotopyRetractionTests](#m0405)<br>[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyClasses](#m0413)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension](#m0424)<br>[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)<br>[HomotopicalAlgebra.Simplicial.KanPostDetection](#m0427)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)<br>[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)<br>[HomotopicalAlgebra.Simplicial.PrecompositionHomotopy](#m0514)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.SmallKanHomotopy](#m0573)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.HomotopyClasses.map_isIso_of_tests` — 全ての区間ホモトピー類によるテストから局所化像の可逆性を判定する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0403"></a>

### m0403 · HomotopicalAlgebra.Simplicial.HomotopyClassesClosed

|項目|記録|
|---|---|
|分類|A|
|ソース|[HomotopyClassesClosed.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/HomotopyClassesClosed.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.HomotopyClassesClosed.equiv`|
|直接import元|[HomotopicalAlgebra.Simplicial.HomotopyRetractionTests](#m0405)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.Simplicial.HomotopyRetractionTests](#m0405)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.HomotopyClassesClosed.equiv` — 閉構造の随伴を区間ホモトピー類の実際の全単射へ降下させる。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0404"></a>

### m0404 · HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[HomotopyEndpointComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/HomotopyEndpointComparison.lean)|
|追加|2026-10-16T13:06:48+09:00 · `25a7578eda56`|
|主な公開宣言|`SerrePositivity.SimplicialModel.HomotopyEndpointComparison.face_zero`<br>`SerrePositivity.SimplicialModel.HomotopyEndpointComparison.homotopy`<br>`SerrePositivity.SimplicialModel.HomotopyEndpointComparison.fixed_endpoints`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyExtension](#m0414)<br>[HomotopicalAlgebra.Simplicial.RetractChainFamily](#m0547)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension](#m0411)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyExtension](#m0414)<br>[HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension](#m0422)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)<br>[HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle](#m0542)<br>[HomotopicalAlgebra.Simplicial.RetractChainFamily](#m0547)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Compare actual selected homotopies relative to both entire endpoint families。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0405"></a>

### m0405 · HomotopicalAlgebra.Simplicial.HomotopyRetractionTests

|項目|記録|
|---|---|
|分類|A|
|ソース|[HomotopyRetractionTests.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/HomotopyRetractionTests.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.HomotopyRetractionTests.post_bijective`|
|直接import元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.HomotopyRetractionTests.post_bijective` — 実際のホモトピーレトラクションから後合成によるホモトピー類の全単射を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0406"></a>

### m0406 · HomotopicalAlgebra.Simplicial.KanActualHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanActualHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanActualHomotopy.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanActualHomotopy.class_eq_iff`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanPostDetection](#m0427)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)<br>[HomotopicalAlgebra.Simplicial.KanPostDetection](#m0427)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanActualHomotopy.class_eq_iff` — Kan値の写像のホモトピー類が等しいことと実際の区間ホモトピーの存在が同値となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0407"></a>

### m0407 · HomotopicalAlgebra.Simplicial.KanComparisonSquare

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanComparisonSquare.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanComparisonSquare.lean)|
|追加|2026-10-17T10:10:39+09:00 · `cf862ed3c08f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanComparisonSquare.Filler`<br>`SerrePositivity.SimplicialModel.KanComparisonSquare.right_second`<br>`SerrePositivity.SimplicialModel.KanComparisonSquare.common_diagonal`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A coherent four-sided comparison using one shared diagonal。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0408"></a>

### m0408 · HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanComparisonTetrahedron.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanComparisonTetrahedron.lean)|
|追加|2026-10-17T10:10:39+09:00 · `cf862ed3c08f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanComparisonTetrahedron.hornFaces`<br>`SerrePositivity.SimplicialModel.KanComparisonTetrahedron.coherence_one`<br>`SerrePositivity.SimplicialModel.KanComparisonTetrahedron.coherence_two`|
|直接import元|[HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy](#m0368)<br>[HomotopicalAlgebra.Simplicial.KanComparisonSquare](#m0407)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy](#m0368)<br>[HomotopicalAlgebra.Simplicial.KanComparisonSquare](#m0407)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Three specified comparison triangles extend to one tetrahedron。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0409"></a>

### m0409 · HomotopicalAlgebra.Simplicial.KanComparisonTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanComparisonTriangle.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanComparisonTriangle.lean)|
|追加|2026-10-17T09:43:15+09:00 · `a5cdb28eea6b`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanComparisonTriangle.Data`<br>`SerrePositivity.SimplicialModel.KanComparisonTriangle.comparison`<br>`SerrePositivity.SimplicialModel.KanComparisonTriangle.family_two`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary](#m0366)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn](#m0369)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport](#m0365)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleBinary](#m0366)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy](#m0368)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn](#m0369)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)<br>[HomotopicalAlgebra.Simplicial.KanComparisonSquare](#m0407)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron](#m0408)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A comparison triangle retains two selected whole interval families。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0410"></a>

### m0410 · HomotopicalAlgebra.Simplicial.KanFiberwiseContraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanFiberwiseContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanFiberwiseContraction.lean)|
|追加|2026-10-17T00:20:33+09:00 · `def378c3c827`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanFiberwiseContraction.exists_homotopy`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanFiberwiseContraction.exists_homotopy` — Kan fibrationの基底上で一定となるようにレトラクションのホモトピーを補正する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0411"></a>

### m0411 · HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanFibrationEndpointExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanFibrationEndpointExtension.lean)|
|追加|2026-10-17T00:20:33+09:00 · `def378c3c827`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanFibrationEndpointExtension.exists_from_zero`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)<br>[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)<br>[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanFibrationEndpointExtension.exists_from_zero` — Kan fibration上の指定区間を始点と基底の区間を保って延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0412"></a>

### m0412 · HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanFibrationLocalizedLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanFibrationLocalizedLifting.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanFibrationLocalizedLifting.of_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanFibrationLocalizedLifting.of_localized_isIso` — Kan基底上の局所化で可逆なKan fibrationはすべての単射に対する右持ち上げ性を持つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0413"></a>

### m0413 · HomotopicalAlgebra.Simplicial.KanHomotopyClasses

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanHomotopyClasses.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanHomotopyClasses.lean)|
|追加|2026-10-16T19:38:32+09:00 · `472439f68f78`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanHomotopyClasses.pre_bijective`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanTestDetection](#m0437)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanHomotopyClasses.pre_bijective` — Kan値の区間ホモトピー類への前合成はanodyne射を全単射へ送る。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0414"></a>

### m0414 · HomotopicalAlgebra.Simplicial.KanHomotopyExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanHomotopyExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanHomotopyExtension.lean)|
|追加|2026-10-16T19:38:32+09:00 · `472439f68f78`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_homotopy`<br>`SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_extension`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanHomotopyClasses](#m0413)<br>[HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension](#m0422)<br>[HomotopicalAlgebra.Simplicial.KanRelativeLifting](#m0431)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyClasses](#m0413)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives](#m0420)<br>[HomotopicalAlgebra.Simplicial.KanRelativeLifting](#m0431)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_homotopy` — anodyne射への制限後のホモトピーから元の両射を結ぶKan値ホモトピーの存在を導く。|
|入口の主張|`SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_extension` — anodyne射に沿って指定したKan値の写像を延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0415"></a>

### m0415 · HomotopicalAlgebra.Simplicial.KanHornFamilyLifting

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanHornFamilyLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanHornFamilyLifting.lean)|
|追加|2026-10-17T10:36:33+09:00 · `cd75e64de421`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanHornFamilyLifting.restriction`<br>`SerrePositivity.SimplicialModel.KanHornFamilyLifting.relativeFamily_earlier`<br>`SerrePositivity.SimplicialModel.KanHornFamilyLifting.relativeFamily_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation](#m0543)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation](#m0372)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornInput](#m0377)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)<br>[HomotopicalAlgebra.Simplicial.NaturalHornFilling](#m0455)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)<br>[HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn](#m0505)<br>[HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation](#m0543)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Lift varying horn families while retaining prescribed earlier whole fillers。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0416"></a>

### m0416 · HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanLocalizedComparisonResolution.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedComparisonResolution.lean)|
|追加|2026-10-17T09:35:05+09:00 · `6ac6247d8399`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedComparisonResolution.obj`<br>`SerrePositivity.SimplicialModel.KanLocalizedComparisonResolution.parameterComparison`<br>`SerrePositivity.SimplicialModel.KanLocalizedComparisonResolution.parameterComparison_naturality`|
|直接import元|[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A relative comparison resolution with one global decoding homotopy。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0417"></a>

### m0417 · HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanLocalizedCoproducts.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedCoproducts.lean)|
|追加|2026-10-17T01:04:36+09:00 · `57354c1ad22f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedCoproducts.actual_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)<br>[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)<br>[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedCoproducts.actual_localized_isIso` — 局所化で可逆な射の実際の余積もモデル構造を仮定せず局所化で可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0418"></a>

### m0418 · HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanLocalizedLeftProper.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedLeftProper.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedLeftProper.localized_isIso`<br>`SerrePositivity.SimplicialModel.KanLocalizedLeftProper.image_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanPushoutCube](#m0430)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanPushoutCube](#m0430)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedLeftProper.localized_isIso` — 任意の局所化同値を単射に沿って押し出した射も局所化同値となる。|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedLeftProper.image_isIso` — anodyne射を反転する任意の関手で単射に沿うpushout比較の像が可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0419"></a>

### m0419 · HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanLocalizedMonoLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedMonoLifting.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedMonoLifting.hasLiftingProperty`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedMonoLifting.hasLiftingProperty` — 局所化で可逆な単射はKan基底上のKan fibrationに対して持ち上げ性を持つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0420"></a>

### m0420 · HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanLocalizedRepresentatives.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedRepresentatives.lean)|
|追加|2026-10-17T01:46:07+09:00 · `0c60cd4bf188`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv`|
|直接import元|[HomotopicalAlgebra.Simplicial.SplitLocalizedDescent](#m0578)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.Simplicial.SplitLocalizedDescent](#m0578)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedRepresentatives.homEquiv` — Kan値への局所化圏の射を実写像のホモトピー類で表す全単射を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0421"></a>

### m0421 · HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanLocalizedTransfinite.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanLocalizedTransfinite.lean)|
|追加|2026-10-17T00:34:39+09:00 · `14726f37f087`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanLocalizedTransfinite.cocone_mem`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanLocalizedTransfinite.cocone_mem` — 局所化で可逆な単射の連続な超限合成も局所化で可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0422"></a>

### m0422 · HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanMonoEndpointExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanMonoEndpointExtension.lean)|
|追加|2026-10-17T00:04:44+09:00 · `59e6c5ae148f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanMonoEndpointExtension.exists_from_zero`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension](#m0411)<br>[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanMonoEndpointExtension.exists_from_zero` — 任意の単射に沿って始点を固定したKan値区間を延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0423"></a>

### m0423 · HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanMonoPushoutEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanMonoPushoutEquivalence.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)<br>[HomotopicalAlgebra.Simplicial.KanPushoutComparison](#m0429)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)<br>[HomotopicalAlgebra.Simplicial.KanPushoutComparison](#m0429)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence.localized_isIso` — 局所化で可逆な単射のpushoutがモデル構造なしで局所化可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0424"></a>

### m0424 · HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanMonoPushoutExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanMonoPushoutExtension.lean)|
|追加|2026-10-17T00:04:44+09:00 · `59e6c5ae148f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanMonoPushoutExtension.exists_extension`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanMonoPushoutExtension.exists_extension` — 局所化で可逆な単射の実pushoutに沿って指定したKan値写像を延長する。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0425"></a>

### m0425 · HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanMonoRelativeHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanMonoRelativeHomotopy.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy.exists_extension`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanMonoRelativeHomotopy.exists_extension` — 局所化で可逆な単射に沿って両端点を保つKan値ホモトピーを延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0426"></a>

### m0426 · HomotopicalAlgebra.Simplicial.KanMonoStrictExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanMonoStrictExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanMonoStrictExtension.lean)|
|追加|2026-10-17T00:04:44+09:00 · `59e6c5ae148f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanMonoStrictExtension.exists_extension`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension](#m0424)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedMonoLifting](#m0419)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension](#m0424)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanMonoStrictExtension.exists_extension` — Kan値ホモトピー類のテストから指定写像の厳密な延長を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0427"></a>

### m0427 · HomotopicalAlgebra.Simplicial.KanPostDetection

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanPostDetection.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanPostDetection.lean)|
|追加|2026-10-17T09:35:05+09:00 · `6ac6247d8399`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanPostDetection.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanPostDetection.localized_isIso` — Kan対象間の射の局所化可逆性を二つの後合成テストで判定する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0428"></a>

### m0428 · HomotopicalAlgebra.Simplicial.KanPullbackDeformation

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanPullbackDeformation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanPullbackDeformation.lean)|
|追加|2026-10-17T00:49:36+09:00 · `c742f0e81db4`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanPullbackDeformation.exists_retraction`<br>`SerrePositivity.SimplicialModel.KanPullbackDeformation.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanPullbackDeformation.exists_retraction` — 強変形レトラクトをKan fibrationに沿って引き戻した実際のレトラクションを構成する。|
|入口の主張|`SerrePositivity.SimplicialModel.KanPullbackDeformation.localized_isIso` — Kan fibrationに沿って引き戻した強変形レトラクトは局所化で可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0429"></a>

### m0429 · HomotopicalAlgebra.Simplicial.KanPushoutComparison

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanPushoutComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanPushoutComparison.lean)|
|追加|2026-10-17T00:43:39+09:00 · `012b8e4f5068`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanPushoutComparison.actual_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanPushoutCube](#m0430)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanPushoutCube](#m0430)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanPushoutComparison.actual_localized_isIso` — 共通の始域の下で単射を持つ図式の局所化比較が実pushoutでも保たれる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0430"></a>

### m0430 · HomotopicalAlgebra.Simplicial.KanPushoutCube

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanPushoutCube.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanPushoutCube.lean)|
|追加|2026-10-17T01:04:36+09:00 · `57354c1ad22f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanPushoutCube.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanPushoutCube.localized_isIso` — 境界も動くpushout cubeの比較が局所化で可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0431"></a>

### m0431 · HomotopicalAlgebra.Simplicial.KanRelativeLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanRelativeLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanRelativeLifting.lean)|
|追加|2026-10-17T00:34:39+09:00 · `14726f37f087`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanRelativeLifting.exists_extension`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy](#m0425)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction](#m0452)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy](#m0425)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanRelativeLifting.exists_extension` — 境界pushout-productの持ち上げ性から指定した相対ホモトピーを延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0432"></a>

### m0432 · HomotopicalAlgebra.Simplicial.KanReplacement

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanReplacement.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanReplacement.lean)|
|追加|2026-10-16T08:54:32+09:00 · `ed6bec42fe4a`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanReplacement.map_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison](#m0060)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.KanLiftAction](#m0102)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterComparison](#m0113)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedLiftActionWeakEquivalence](#m0123)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters](#m0124)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison](#m0127)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionLiftAction](#m0128)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowActionTransport](#m0277)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPostcomposition](#m0308)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftPrecomposition](#m0309)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping](#m0331)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanReplacement.map_weakEquivalence` — 指定した値モデルで構成した関手的Kan置換は弱同値を保つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0433"></a>

### m0433 · HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanRestrictionEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanRestrictionEquivalence.lean)|
|追加|2026-10-17T09:35:05+09:00 · `6ac6247d8399`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanRestrictionEquivalence.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanRestrictionEquivalence.localized_isIso` — 局所化可逆な射に沿うKan値内部Homの制限も局所化可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0434"></a>

### m0434 · HomotopicalAlgebra.Simplicial.KanRestrictionLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanRestrictionLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanRestrictionLifting.lean)|
|追加|2026-10-17T00:28:54+09:00 · `d86cd528a779`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanRestrictionLifting.all_mono_rlp`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy](#m0425)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanHornFamilyLifting](#m0415)<br>[HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy](#m0425)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanRestrictionLifting.all_mono_rlp` — 局所化可逆な単射に沿うKan値内部Homの制限はすべての単射に対する右持ち上げ性を持つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0435"></a>

### m0435 · HomotopicalAlgebra.Simplicial.KanRetractionRightLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanRetractionRightLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanRetractionRightLifting.lean)|
|追加|2026-10-17T00:20:33+09:00 · `def378c3c827`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanRetractionRightLifting.of_homotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanRetractionRightLifting.of_homotopy` — Kan fibrationの実レトラクションホモトピーからすべての単射に対する右持ち上げ性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0436"></a>

### m0436 · HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanSequentialColimitComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanSequentialColimitComparison.lean)|
|追加|2026-10-17T01:13:22+09:00 · `1fe081476cdf`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanSequentialColimitComparison.actual_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanSequentialColimitComparison.actual_localized_isIso` — 逐次図式の局所化可逆な比較は実際の余極限上でも局所化可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0437"></a>

### m0437 · HomotopicalAlgebra.Simplicial.KanTestDetection

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanTestDetection.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanTestDetection.lean)|
|追加|2026-10-16T23:58:11+09:00 · `15e2b83931ba`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanTestDetection.anodyneQ_isIso_iff_tests`<br>`SerrePositivity.SimplicialModel.KanTestDetection.map_isIso_of_tests`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.AnodyneNonempty](#m0345)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.AnodyneNonempty](#m0345)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)<br>[HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting](#m0412)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)<br>[HomotopicalAlgebra.Simplicial.KanMonoStrictExtension](#m0426)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionLifting](#m0434)<br>[HomotopicalAlgebra.Simplicial.KanTestLiftingClass](#m0438)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanTestDetection.anodyneQ_isIso_iff_tests` — anodyne局所化での可逆性は全Kan値ホモトピー類のテストで判定できる。|
|入口の主張|`SerrePositivity.SimplicialModel.KanTestDetection.map_isIso_of_tests` — 全Kan値のホモトピー類テストからanodyne局所化像の可逆性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0438"></a>

### m0438 · HomotopicalAlgebra.Simplicial.KanTestLiftingClass

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanTestLiftingClass.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanTestLiftingClass.lean)|
|追加|2026-10-17T00:34:39+09:00 · `14726f37f087`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanTestLiftingClass.localizedMonos_eq`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts](#m0417)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite](#m0421)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalKanTests](#m0384)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts](#m0417)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedTransfinite](#m0421)<br>[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)<br>[HomotopicalAlgebra.Simplicial.LocalizedMonoReedy](#m0448)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanTestLiftingClass.localizedMonos_eq` — 局所化可逆な単射を固定した左持ち上げクラスとの交わりとして特徴付ける。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0439"></a>

### m0439 · HomotopicalAlgebra.Simplicial.KanTriangleFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[KanTriangleFamily.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanTriangleFamily.lean)|
|追加|2026-10-16T11:15:21+09:00 · `462a22b3c87c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanTriangleFamily.parameter`<br>`SerrePositivity.SimplicialModel.KanTriangleFamily.transported_initial`<br>`SerrePositivity.SimplicialModel.KanTriangleFamily.reindexHomotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Kan extensions of triangle families and relative reindexing comparisons。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0440"></a>

### m0440 · HomotopicalAlgebra.Simplicial.KanTwoHornLift

|項目|記録|
|---|---|
|分類|A|
|ソース|[KanTwoHornLift.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/KanTwoHornLift.lean)|
|追加|2026-10-17T00:20:33+09:00 · `def378c3c827`|
|主な公開宣言|`SerrePositivity.SimplicialModel.KanTwoHornLift.exists_triangle`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.KanTwoHornLift.exists_triangle` — 指定した基底三角形の上で外側二次hornを充填する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0441"></a>

### m0441 · HomotopicalAlgebra.Simplicial.LargeParameterExtension

|項目|記録|
|---|---|
|分類|A|
|ソース|[LargeParameterExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LargeParameterExtension.lean)|
|追加|2026-10-16T11:58:45+09:00 · `bfdca7e488b2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LargeParameterExtension.relativeExtend`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.Simplicial.BoundaryFillerLifting](#m0353)<br>[HomotopicalAlgebra.Simplicial.LargeParameterHomotopy](#m0442)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.Simplicial.LargeParameterHomotopy](#m0442)<br>[HomotopicalAlgebra.Simplicial.LargeParameterMapping](#m0443)<br>[HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice](#m0444)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.LargeParameterExtension.relativeExtend` — 小さい比較空間の宇宙liftを値として大きいパラメータ上の指定族を相対延長する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0442"></a>

### m0442 · HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[LargeParameterHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LargeParameterHomotopy.lean)|
|追加|2026-10-16T12:13:35+09:00 · `f34b16b8364a`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LargeParameterHomotopy.homotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.Simplicial.LargeParameterMapping](#m0443)<br>[HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice](#m0444)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy](#m0177)<br>[HomotopicalAlgebra.Simplicial.CurriedHomotopy](#m0376)<br>[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)<br>[HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension](#m0411)<br>[HomotopicalAlgebra.Simplicial.KanHomotopyExtension](#m0414)<br>[HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension](#m0422)<br>[HomotopicalAlgebra.Simplicial.KanRelativeLifting](#m0431)<br>[HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice](#m0444)<br>[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction](#m0452)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.LargeParameterHomotopy.homotopy` — 大きいパラメータから小さい可縮な比較空間の宇宙liftへの区間ホモトピーを構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0443"></a>

### m0443 · HomotopicalAlgebra.Simplicial.LargeParameterMapping

|項目|記録|
|---|---|
|分類|A|
|ソース|[LargeParameterMapping.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LargeParameterMapping.lean)|
|追加|2026-10-16T12:22:50+09:00 · `b2a1d411792b`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LargeParameterMapping.fillFaces`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.LargeParameterMapping.fillFaces` — 大きいパラメータを持つ写像空間で互換な全面を充填する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0444"></a>

### m0444 · HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice

|項目|記録|
|---|---|
|分類|B|
|ソース|[LargeParameterRelativeChoice.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LargeParameterRelativeChoice.lean)|
|追加|2026-10-16T12:51:18+09:00 · `515511d5cd33`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LargeParameterRelativeChoice.terminal_lifting`<br>`SerrePositivity.SimplicialModel.LargeParameterRelativeChoice.homotopy`<br>`SerrePositivity.SimplicialModel.LargeParameterRelativeChoice.homotopy_relative`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All-dimensional relative choices over large parameters。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0445"></a>

### m0445 · HomotopicalAlgebra.Simplicial.LargeParameterSquare

|項目|記録|
|---|---|
|分類|B|
|ソース|[LargeParameterSquare.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LargeParameterSquare.lean)|
|追加|2026-10-16T12:32:15+09:00 · `561db7ce10aa`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LargeParameterSquare.point`<br>`SerrePositivity.SimplicialModel.LargeParameterSquare.right_second`<br>`SerrePositivity.SimplicialModel.LargeParameterSquare.common_diagonal`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.CurriedHomotopy](#m0376)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleDegeneracy](#m0368)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleHorn](#m0369)<br>[HomotopicalAlgebra.Simplicial.CurriedHomotopy](#m0376)<br>[HomotopicalAlgebra.Simplicial.KanActualHomotopy](#m0406)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanFiberwiseContraction](#m0410)<br>[HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence](#m0423)<br>[HomotopicalAlgebra.Simplicial.KanPullbackDeformation](#m0428)<br>[HomotopicalAlgebra.Simplicial.KanRetractionRightLifting](#m0435)<br>[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation](#m0546)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Fill a square retaining four selected global homotopies。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0446"></a>

### m0446 · HomotopicalAlgebra.Simplicial.LatchingDegeneracies

|項目|記録|
|---|---|
|分類|A|
|ソース|[LatchingDegeneracies.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LatchingDegeneracies.lean)|
|追加|2026-10-16T08:26:05+09:00 · `27b29cedd054`|
|主な公開宣言|`SerrePositivity.SimplicialLatching.common_refinement`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.LatchingMonomorphisms](#m0447)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.LatchingMonomorphisms](#m0447)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialLatching.common_refinement` — 二つの退化表示に共通の細分を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0447"></a>

### m0447 · HomotopicalAlgebra.Simplicial.LatchingMonomorphisms

|項目|記録|
|---|---|
|分類|A|
|ソース|[LatchingMonomorphisms.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LatchingMonomorphisms.lean)|
|追加|2026-10-16T08:26:05+09:00 · `27b29cedd054`|
|主な公開宣言|`SerrePositivity.SimplicialLatching.comparison_mono`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy](#m0351)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BisimplicialCofibrancy](#m0351)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialLatching.comparison_mono` — 単体的集合のlatching比較射は単射となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0448"></a>

### m0448 · HomotopicalAlgebra.Simplicial.LocalizedMonoReedy

|項目|記録|
|---|---|
|分類|A|
|ソース|[LocalizedMonoReedy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LocalizedMonoReedy.lean)|
|追加|2026-10-17T08:57:13+09:00 · `916916fe36e7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LocalizedMonoReedy.reedy_iff`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence](#m0385)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.LocalizedMonoReedy.reedy_iff` — Reedy局所化単射をReedy単射かつ各成分の局所化同値として特徴付ける。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0449"></a>

### m0449 · HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice

|項目|記録|
|---|---|
|分類|B|
|ソース|[LocalizedRelativeChoice.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/LocalizedRelativeChoice.lean)|
|追加|2026-10-17T03:50:44+09:00 · `41479ac9d7b0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.LocalizedRelativeChoice.restrictionSection`<br>`SerrePositivity.SimplicialModel.LocalizedRelativeChoice.interval`<br>`SerrePositivity.SimplicialModel.LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.KanHornFamilyLifting](#m0415)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Contractible actual extension spaces along a localized mono equivalence。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0450"></a>

### m0450 · HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[MappingPrecompositionRetraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/MappingPrecompositionRetraction.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.MappingPrecompositionRetraction.pullback_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.MappingPrecompositionRetraction.pullback_localized_isIso` — 基底上の強変形レトラクトを内部Homへ移しそのpullbackの局所化可逆性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0451"></a>

### m0451 · HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization

|項目|記録|
|---|---|
|分類|A|
|ソース|[MonoLocalizedFactorization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/MonoLocalizedFactorization.lean)|
|追加|2026-10-17T00:43:39+09:00 · `012b8e4f5068`|
|主な公開宣言|`SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right_all_mono_rlp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts](#m0417)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)<br>[HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization](#m0554)<br>[HomotopicalAlgebra.Simplicial.UnderMonoBrown](#m0587)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedComparisonResolution](#m0416)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts](#m0417)<br>[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)<br>[HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization](#m0554)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLift](#m0555)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)<br>[HomotopicalAlgebra.Simplicial.UnderMonoBrown](#m0587)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.MonoLocalizedFactorization.right_all_mono_rlp` — モデル構造不要の関手的単射分解の右因子はすべての単射に対する右持ち上げ性を持つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0452"></a>

### m0452 · HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[MonoRightLiftingContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/MonoRightLiftingContraction.lean)|
|追加|2026-10-17T00:43:39+09:00 · `012b8e4f5068`|
|主な公開宣言|`SerrePositivity.SimplicialModel.MonoRightLiftingContraction.exists_vertical_contraction`|
|直接import元|[HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization](#m0356)<br>[HomotopicalAlgebra.Simplicial.BoundaryRightColimit](#m0357)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)<br>[HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization](#m0451)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization](#m0356)<br>[HomotopicalAlgebra.Simplicial.BoundaryRightColimit](#m0357)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)<br>[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)<br>[HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization](#m0451)<br>[HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy](#m0453)<br>[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.MonoRightLiftingContraction.exists_vertical_contraction` — すべての単射に対する右持ち上げ性を持つ射の切断に基底上で一定の収縮を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0453"></a>

### m0453 · HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[MonoRightLiftingRelativeHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/MonoRightLiftingRelativeHomotopy.lean)|
|追加|2026-10-17T04:00:54+09:00 · `40f85bde91b4`|
|主な公開宣言|`SerrePositivity.SimplicialModel.MonoRightLiftingRelativeHomotopy.exists_strong_contraction`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.RelativeProductLifting](#m0544)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.MonoRightLiftingRelativeHomotopy.exists_strong_contraction` — すべての単射に対する右持ち上げ性を持つ射の切断上で固定された強い収縮を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0454"></a>

### m0454 · HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[MonoRightPushoutEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/MonoRightPushoutEquivalence.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence.localized_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper](#m0418)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.MonoRightPushoutEquivalence.localized_isIso` — 境界に右持ち上げ性を持つ射の単射に沿うpushoutは局所化で可逆となる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0455"></a>

### m0455 · HomotopicalAlgebra.Simplicial.NaturalHornFilling

|項目|記録|
|---|---|
|分類|B|
|ソース|[NaturalHornFilling.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NaturalHornFilling.lean)|
|追加|2026-10-17T10:52:25+09:00 · `880c661b5d70`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NaturalHornFilling.transpose_precompose`<br>`SerrePositivity.SimplicialModel.NaturalHornFilling.family_reindex`<br>`SerrePositivity.SimplicialModel.NaturalHornFilling.fill_degenerate`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transpose one horn filling operation into strictly natural parameter families。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0456"></a>

### m0456 · HomotopicalAlgebra.Simplicial.NerveArrowComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveArrowComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveArrowComparison.lean)|
|追加|2026-10-16T15:57:48+09:00 · `2e786e3d21f9`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveArrowComparison.source`<br>`SerrePositivity.SimplicialModel.NerveArrowComparison.left_boundary`<br>`SerrePositivity.SimplicialModel.NerveArrowComparison.right_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The two whole coherent endpoint systems of comparison along every arrow。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0457"></a>

### m0457 · HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveArrowComparisonComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveArrowComparisonComposition.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveArrowComparisonComposition.leftAlong`<br>`SerrePositivity.SimplicialModel.NerveArrowComparisonComposition.left_reindex`<br>`SerrePositivity.SimplicialModel.NerveArrowComparisonComposition.right_reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Exact endpoint calculus for composable changes of coherent centers。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0458"></a>

### m0458 · HomotopicalAlgebra.Simplicial.NerveBinaryBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBinaryBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBinaryBoundary.lean)|
|追加|2026-10-16T16:06:38+09:00 · `da59b69519b7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBinaryBoundary.glue`<br>`SerrePositivity.SimplicialModel.NerveBinaryBoundary.glue_right`<br>`SerrePositivity.SimplicialModel.NerveBinaryBoundary.hom_ext`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Gluing two whole moving systems on a pointwise binary coproduct diagram。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0459"></a>

### m0459 · HomotopicalAlgebra.Simplicial.NerveBiparameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBiparameter.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBiparameter.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBiparameter.operator_zero`<br>`SerrePositivity.SimplicialModel.NerveBiparameter.compatibility`<br>`SerrePositivity.SimplicialModel.NerveBiparameter.reindex_compatibility`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparison](#m0456)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)<br>[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderBoundary](#m0468)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Changing parameters at the first endpoint and values at the last endpoint。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0460"></a>

### m0460 · HomotopicalAlgebra.Simplicial.NerveBiparameterComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBiparameterComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBiparameterComposition.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBiparameterMaps.targetMap_comp`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.reindex_expand`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.expand_mapTarget`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedReassociationEquality](#m0324)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole-system composition laws for actual parameter and value transports。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0461"></a>

### m0461 · HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBiparameterEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBiparameterEvaluation.lean)|
|追加|2026-10-16T15:57:48+09:00 · `2e786e3d21f9`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBiparameterMaps.name_evaluate`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.evaluate_restrict`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.evaluate_reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Recovering actual whole maps after parameter and value transport。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0462"></a>

### m0462 · HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBiparameterMapLaws.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBiparameterMapLaws.lean)|
|追加|2026-10-16T15:57:48+09:00 · `2e786e3d21f9`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBiparameterMaps.target_restriction`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.restrict_natural`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.mapTarget_natural`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparison](#m0456)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparison](#m0456)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transport laws retaining canonical whole moving boundaries。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0463"></a>

### m0463 · HomotopicalAlgebra.Simplicial.NerveBiparameterMaps

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBiparameterMaps.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBiparameterMaps.lean)|
|追加|2026-10-16T15:46:16+09:00 · `9d61c8af5c20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBiparameterMaps.restriction`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.start_map`<br>`SerrePositivity.SimplicialModel.NerveBiparameterMaps.reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparison](#m0456)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparisonComposition](#m0457)<br>[HomotopicalAlgebra.Simplicial.NerveBinaryBoundary](#m0458)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderBoundary](#m0468)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual reindexing and parameter/value maps of two-endpoint coherent families。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0464"></a>

### m0464 · HomotopicalAlgebra.Simplicial.NerveBoundaryExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveBoundaryExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveBoundaryExtension.lean)|
|追加|2026-10-16T14:46:40+09:00 · `79fe1764d240`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveBoundaryExtension.Compatible`<br>`SerrePositivity.SimplicialModel.NerveBoundaryExtension.extend_boundary`<br>`SerrePositivity.SimplicialModel.NerveBoundaryExtension.extend_face`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent higher parameter extensions with all whole facet systems fixed。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0465"></a>

### m0465 · HomotopicalAlgebra.Simplicial.NerveCoherentExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveCoherentExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveCoherentExtension.lean)|
|追加|2026-10-16T14:08:11+09:00 · `4dca7af70c9c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveCoherentExtension.projection`<br>`SerrePositivity.SimplicialModel.NerveCoherentExtension.extend_initial`<br>`SerrePositivity.SimplicialModel.NerveCoherentExtension.extend_component`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative coherent choice on every chain of a possibly large category。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0466"></a>

### m0466 · HomotopicalAlgebra.Simplicial.NerveCoherentFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveCoherentFamily.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveCoherentFamily.lean)|
|追加|2026-10-16T13:43:22+09:00 · `1de52e9af25a`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveCoherentFamily.inverse`<br>`SerrePositivity.SimplicialModel.NerveCoherentFamily.ofPoint_component`<br>`SerrePositivity.SimplicialModel.NerveCoherentFamily.map`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentReindex](#m0467)<br>[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameter](#m0459)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentExtension](#m0465)<br>[HomotopicalAlgebra.Simplicial.NerveCoherentReindex](#m0467)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveLowerExtension](#m0478)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent families with values at the changing endpoint of a chain。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0467"></a>

### m0467 · HomotopicalAlgebra.Simplicial.NerveCoherentReindex

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveCoherentReindex.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveCoherentReindex.lean)|
|追加|2026-10-16T15:09:35+09:00 · `673dd59a1084`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveCoherentReindex.index`<br>`SerrePositivity.SimplicialModel.NerveCoherentReindex.reindex`<br>`SerrePositivity.SimplicialModel.NerveCoherentReindex.reindex_component`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMaps](#m0463)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Reindexing whole coherent systems along actual functors of center categories。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0468"></a>

### m0468 · HomotopicalAlgebra.Simplicial.NerveCylinderBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveCylinderBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveCylinderBoundary.lean)|
|追加|2026-10-16T15:46:16+09:00 · `9d61c8af5c20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveCylinderBoundary.product`<br>`SerrePositivity.SimplicialModel.NerveCylinderBoundary.system_endpoints`<br>`SerrePositivity.SimplicialModel.NerveCylinderBoundary.system_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The union of the entire endpoint and vertex boundaries of a moving cylinder。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0469"></a>

### m0469 · HomotopicalAlgebra.Simplicial.NerveCylinderExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveCylinderExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveCylinderExtension.lean)|
|追加|2026-10-16T15:46:16+09:00 · `9d61c8af5c20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveCylinderExtension.extend`<br>`SerrePositivity.SimplicialModel.NerveCylinderExtension.extend_endpoints`<br>`SerrePositivity.SimplicialModel.NerveCylinderExtension.extend_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative moving extension retaining both whole cylinder boundary systems。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0470"></a>

### m0470 · HomotopicalAlgebra.Simplicial.NerveDiagramExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveDiagramExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveDiagramExtension.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveDiagramExtension.InvertsInverse`<br>`SerrePositivity.SimplicialModel.NerveDiagramExtension.extend_restrict`<br>`SerrePositivity.SimplicialModel.NerveDiagramExtension.extend_component`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative coherent lifting for general inverse-inverting nerve value diagrams。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0471"></a>

### m0471 · HomotopicalAlgebra.Simplicial.NerveEvaluationLaws

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveEvaluationLaws.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveEvaluationLaws.lean)|
|追加|2026-10-16T16:14:50+09:00 · `1259086cfc03`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveEvaluationLaws.restriction`<br>`SerrePositivity.SimplicialModel.NerveEvaluationLaws.natural`<br>`SerrePositivity.SimplicialModel.NerveEvaluationLaws.expand`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit](#m0281)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual objectwise evaluation of whole restriction and natural-boundary equations。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0472"></a>

### m0472 · HomotopicalAlgebra.Simplicial.NerveFillerExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveFillerExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveFillerExtension.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveFillerExtension.point`<br>`SerrePositivity.SimplicialModel.NerveFillerExtension.extendVertices`<br>`SerrePositivity.SimplicialModel.NerveFillerExtension.extendVertices_point`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole coherent systems from objectwise boundary fillers, with no model structure。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0473"></a>

### m0473 · HomotopicalAlgebra.Simplicial.NerveFirstChoice

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveFirstChoice.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveFirstChoice.lean)|
|追加|2026-10-16T21:02:18+09:00 · `5d02b7b07e52`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveFirstChoice.values`<br>`SerrePositivity.SimplicialModel.NerveFirstChoice.reindex_compatibility`<br>`SerrePositivity.SimplicialModel.NerveFirstChoice.constant`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone](#m0148)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstAction](#m0163)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRowDiagram](#m0217)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalCone](#m0231)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalHomotopy](#m0233)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarConeDiagram](#m0289)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFirstAction](#m0291)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarFrameSquares](#m0292)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowDiagram](#m0294)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowOperators](#m0296)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent choices at the first endpoint for contravariant diagrams。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0474"></a>

### m0474 · HomotopicalAlgebra.Simplicial.NerveInitialImage

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveInitialImage.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveInitialImage.lean)|
|追加|2026-10-16T23:46:40+09:00 · `3d22bdf25143`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveInitialImage.contraction`<br>`SerrePositivity.SimplicialModel.NerveInitialImage.terminalImageIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexNerveStandard](#m0567)<br>[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexNerveStandard](#m0567)<br>[HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction](#m0576)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|An initial object gives a model-free localized contraction of its nerve。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0475"></a>

### m0475 · HomotopicalAlgebra.Simplicial.NerveIntervalBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveIntervalBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveIntervalBoundary.lean)|
|追加|2026-10-16T14:40:20+09:00 · `78b8b659ef20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveIntervalBoundary.constant`<br>`SerrePositivity.SimplicialModel.NerveIntervalBoundary.ofEdges_zero`<br>`SerrePositivity.SimplicialModel.NerveIntervalBoundary.ofEdges_one`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent interval boundaries glued from two whole endpoint systems。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0476"></a>

### m0476 · HomotopicalAlgebra.Simplicial.NerveLargeParameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveLargeParameter.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveLargeParameter.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveLargeParameter.lifted`<br>`SerrePositivity.SimplicialModel.NerveLargeParameter.relative_boundary`<br>`SerrePositivity.SimplicialModel.NerveLargeParameter.relative_restrict`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent whole large-parameter families with small original value spaces。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0477"></a>

### m0477 · HomotopicalAlgebra.Simplicial.NerveLargeSampling

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveLargeSampling.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveLargeSampling.lean)|
|追加|2026-10-16T18:12:55+09:00 · `6bfedb29b930`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveLargeSampling.moving`<br>`SerrePositivity.SimplicialModel.NerveLargeSampling.system_restrict`<br>`SerrePositivity.SimplicialModel.NerveLargeSampling.family_restrict`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallFamilies](#m0058)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Small full test families of a coherent system with a large constant parameter。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0478"></a>

### m0478 · HomotopicalAlgebra.Simplicial.NerveLowerExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveLowerExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveLowerExtension.lean)|
|追加|2026-10-16T14:15:37+09:00 · `9dc93b11a0f3`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveLowerExtension.LowerSystem`<br>`SerrePositivity.SimplicialModel.NerveLowerExtension.extendVertices`<br>`SerrePositivity.SimplicialModel.NerveLowerExtension.extendVertices_point`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)<br>[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.NervePrescribedCells](#m0488)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent extension retaining all specified lower-dimensional chain data。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0479"></a>

### m0479 · HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMonomorphismLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMonomorphismLifting.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMonomorphismLifting.valueMap`<br>`SerrePositivity.SimplicialModel.NerveMonomorphismLifting.extend_restrict`<br>`SerrePositivity.SimplicialModel.NerveMonomorphismLifting.extend_component`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative coherent lifting without a model structure in the value universe。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0480"></a>

### m0480 · HomotopicalAlgebra.Simplicial.NerveMovingBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMovingBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMovingBoundary.lean)|
|追加|2026-10-16T17:18:29+09:00 · `da71d1d985f6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMovingBoundary.Compatible`<br>`SerrePositivity.SimplicialModel.NerveMovingBoundary.hom_ext`<br>`SerrePositivity.SimplicialModel.NerveMovingBoundary.boundary_vertices`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Gluing all whole facet systems with a moving parameter and moving values。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0481"></a>

### m0481 · HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMovingFamilyFit.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMovingFamilyFit.lean)|
|追加|2026-10-16T16:14:50+09:00 · `1259086cfc03`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMovingFamilyFit.lower_recover`<br>`SerrePositivity.SimplicialModel.NerveMovingFamilyFit.extend_evaluate`<br>`SerrePositivity.SimplicialModel.NerveMovingFamilyFit.extend_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderFamilyFit](#m0281)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole family compatibility derived from actual objectwise boundary equations。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0482"></a>

### m0482 · HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMovingIntervalBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMovingIntervalBoundary.lean)|
|追加|2026-10-16T16:06:38+09:00 · `da59b69519b7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMovingIntervalBoundary.point`<br>`SerrePositivity.SimplicialModel.NerveMovingIntervalBoundary.glue_horizontal`<br>`SerrePositivity.SimplicialModel.NerveMovingIntervalBoundary.common_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual interval boundaries for changing tuple parameters, with a shared whole vertex system。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0483"></a>

### m0483 · HomotopicalAlgebra.Simplicial.NerveMovingParameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMovingParameter.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMovingParameter.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMovingParameter.lifted`<br>`SerrePositivity.SimplicialModel.NerveMovingParameter.evaluate`<br>`SerrePositivity.SimplicialModel.NerveMovingParameter.extendFamilies_evaluate`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedCenterActionWeakEquivalence](#m0112)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagram](#m0317)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole coherent families for parameters moving with the center。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0484"></a>

### m0484 · HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveMovingParameterRelative.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveMovingParameterRelative.lean)|
|追加|2026-10-16T15:21:41+09:00 · `ff1ca062dd8e`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveMovingParameterRelative.restriction`<br>`SerrePositivity.SimplicialModel.NerveMovingParameterRelative.extendFamilies_evaluate`<br>`SerrePositivity.SimplicialModel.NerveMovingParameterRelative.extendFamilies_boundary`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Retaining coherent moving boundaries in changing parameter diagrams。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0485"></a>

### m0485 · HomotopicalAlgebra.Simplicial.NerveNaturalBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveNaturalBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveNaturalBoundary.lean)|
|追加|2026-10-16T15:32:44+09:00 · `fb287c15ee25`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveNaturalBoundary.whole`<br>`SerrePositivity.SimplicialModel.NerveNaturalBoundary.whole_zero`<br>`SerrePositivity.SimplicialModel.NerveNaturalBoundary.ofNatTrans_zero`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveArrowComparison](#m0456)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole coherent moving boundaries induced by actual natural transformations。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0486"></a>

### m0486 · HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveNaturalBoundaryTransport.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveNaturalBoundaryTransport.lean)|
|追加|2026-10-16T17:26:25+09:00 · `1c295db1585c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport.restrict_square`<br>`SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport.horizontal_square`<br>`SerrePositivity.SimplicialModel.NerveNaturalBoundaryTransport.horizontal_fixed`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Transporting a fixed whole natural boundary through actual parameter squares。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0487"></a>

### m0487 · HomotopicalAlgebra.Simplicial.NerveParameterExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveParameterExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveParameterExtension.lean)|
|追加|2026-10-16T14:31:18+09:00 · `3d6feb1b6039`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveParameterExtension.cotensor`<br>`SerrePositivity.SimplicialModel.NerveParameterExtension.extendFamilies_evaluate`<br>`SerrePositivity.SimplicialModel.NerveParameterExtension.extendFamilies_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Coherent parameter extensions retaining prescribed families and coherent boundaries。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0488"></a>

### m0488 · HomotopicalAlgebra.Simplicial.NervePrescribedCells

|項目|記録|
|---|---|
|分類|B|
|ソース|[NervePrescribedCells.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NervePrescribedCells.lean)|
|追加|2026-10-16T14:21:16+09:00 · `c9d850e647cb`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NervePrescribedCells.Data`<br>`SerrePositivity.SimplicialModel.NervePrescribedCells.extend_chain`<br>`SerrePositivity.SimplicialModel.NervePrescribedCells.extend_restrict`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Retain independently specified cells with explicit face and degeneracy conditions。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0489"></a>

### m0489 · HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveProductEndpointTransport.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveProductEndpointTransport.lean)|
|追加|2026-10-16T16:59:51+09:00 · `7583f39c3187`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveProductEndpointTransport.mapTarget_restrict`<br>`SerrePositivity.SimplicialModel.NerveProductEndpointTransport.mapTarget_endpoint`<br>`SerrePositivity.SimplicialModel.NerveProductEndpointTransport.restrict_endpoint`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole endpoint equations survive the actual parameter and value transports。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0490"></a>

### m0490 · HomotopicalAlgebra.Simplicial.NerveProductParameter

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveProductParameter.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveProductParameter.lean)|
|追加|2026-10-16T16:06:38+09:00 · `da59b69519b7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveProductParameter.projection`<br>`SerrePositivity.SimplicialModel.NerveProductParameter.expand_horizontal`<br>`SerrePositivity.SimplicialModel.NerveProductParameter.expand_natural`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary](#m0279)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEndpointCompatibility](#m0319)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedRawEndpoints](#m0322)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedVertexRestrictions](#m0329)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalEndpoints](#m0334)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalVertices](#m0335)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterComposition](#m0460)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)<br>[HomotopicalAlgebra.Simplicial.NerveMovingIntervalBoundary](#m0482)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundaryTransport](#m0486)<br>[HomotopicalAlgebra.Simplicial.NerveProductEndpointTransport](#m0489)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Supplementary constant parameters in whole moving coherent systems。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0491"></a>

### m0491 · HomotopicalAlgebra.Simplicial.NervePushoutBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NervePushoutBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NervePushoutBoundary.lean)|
|追加|2026-10-16T15:46:16+09:00 · `9d61c8af5c20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NervePushoutBoundary.parameter`<br>`SerrePositivity.SimplicialModel.NervePushoutBoundary.glue_left`<br>`SerrePositivity.SimplicialModel.NervePushoutBoundary.glue_right`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderBoundary](#m0468)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangleBoundary](#m0327)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderBoundary](#m0468)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Gluing whole coherent moving parameter systems along a diagram pushout。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0492"></a>

### m0492 · HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveRelativeNaturalBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveRelativeNaturalBoundary.lean)|
|追加|2026-10-16T15:32:44+09:00 · `fb287c15ee25`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary.compatible`<br>`SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary.extend_evaluate`<br>`SerrePositivity.SimplicialModel.NerveRelativeNaturalBoundary.extend_boundary`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Moving relative extension with a prescribed strict natural boundary。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0493"></a>

### m0493 · HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveRelativeValueExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveRelativeValueExtension.lean)|
|追加|2026-10-16T14:31:18+09:00 · `3d6feb1b6039`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveRelativeValueExtension.valueMap`<br>`SerrePositivity.SimplicialModel.NerveRelativeValueExtension.extend_restrict`<br>`SerrePositivity.SimplicialModel.NerveRelativeValueExtension.extend_component`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative coherent lifting over a prescribed whole value system。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0494"></a>

### m0494 · HomotopicalAlgebra.Simplicial.NerveSmallFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[NerveSmallFamilies.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NerveSmallFamilies.lean)|
|追加|2026-10-16T17:42:17+09:00 · `c543585aa9ca`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NerveSmallFamilies.family`<br>`SerrePositivity.SimplicialModel.NerveSmallFamilies.point_lift`<br>`SerrePositivity.SimplicialModel.NerveSmallFamilies.family_restrict`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedAction](#m0129)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveSmallAction](#m0131)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Read whole moving coherent systems back as original-universe chain families。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0495"></a>

### m0495 · HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedComparisonSquare.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedComparisonSquare.lean)|
|追加|2026-10-17T11:05:09+09:00 · `6377d775b760`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedComparisonSquare.build`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonSquare.left_reindex`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonSquare.right_reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A chosen comparison disc strictly natural in the whole source parameter。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0496"></a>

### m0496 · HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedComparisonTetrahedron.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedComparisonTetrahedron.lean)|
|追加|2026-10-17T11:05:09+09:00 · `6377d775b760`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedComparisonTetrahedron.tetrahedron`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonTetrahedron.compare`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonTetrahedron.degenerate`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A normalized comparison tetrahedron strictly natural in its source parameter。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0497"></a>

### m0497 · HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedComparisonTriangle.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedComparisonTriangle.lean)|
|追加|2026-10-17T10:52:25+09:00 · `880c661b5d70`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedComparisonTriangle.triangle`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonTriangle.diagonal_comparison`<br>`SerrePositivity.SimplicialModel.NormalizedComparisonTriangle.compare`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonSquare](#m0495)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A comparison triangle strictly natural in the original source parameter。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0498"></a>

### m0498 · HomotopicalAlgebra.Simplicial.NormalizedHornFilling

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornFilling.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornFilling.lean)|
|追加|2026-10-17T11:00:32+09:00 · `7ed4a33f06d6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornFilling.compatible`<br>`SerrePositivity.SimplicialModel.NormalizedHornFilling.compare`<br>`SerrePositivity.SimplicialModel.NormalizedHornFilling.triangle_section`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison](#m0501)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One horn filling operation preserves all degeneracies in every dimension。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0499"></a>

### m0499 · HomotopicalAlgebra.Simplicial.NormalizedHornInputMap

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornInputMap.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornInputMap.lean)|
|追加|2026-10-17T11:23:20+09:00 · `8f460a197d13`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornInputMap.boundary_naturality`<br>`SerrePositivity.SimplicialModel.NormalizedHornInputMap.map_id`<br>`SerrePositivity.SimplicialModel.NormalizedHornInputMap.map_comp`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Degenerate horn input unions are strictly functorial in the target。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0500"></a>

### m0500 · HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornTargetAssociativity.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornTargetAssociativity.lean)|
|追加|2026-10-17T11:28:48+09:00 · `5ab0918e8610`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornTargetAssociativity.faces`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetAssociativity.family_face`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetAssociativity.family_degenerate`|
|直接import元|なし|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Three target maps give a whole compatible tetrahedral boundary。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0501"></a>

### m0501 · HomotopicalAlgebra.Simplicial.NormalizedHornTargetComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornTargetComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornTargetComparison.lean)|
|追加|2026-10-17T11:15:26+09:00 · `32c6add882dd`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornTargetComparison.sourceThenMap`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetComparison.evaluation_reindex`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetComparison.family_degenerate`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornInputMap](#m0499)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces](#m0503)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Target comparison of normalized horn filling operations。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0502"></a>

### m0502 · HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornTargetComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornTargetComposition.lean)|
|追加|2026-10-17T11:23:20+09:00 · `8f460a197d13`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornTargetComposition.middle`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetComposition.family_face`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetComposition.family_degenerate`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces](#m0503)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces](#m0503)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A composition triangle retains all three selected target comparisons。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0503"></a>

### m0503 · HomotopicalAlgebra.Simplicial.NormalizedHornTargetFaces

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornTargetFaces.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornTargetFaces.lean)|
|追加|2026-10-17T11:28:48+09:00 · `5ab0918e8610`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornTargetFaces.zero`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetFaces.one`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetFaces.two`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Whole faces of the selected target composition triangle。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0504"></a>

### m0504 · HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedHornTargetIdentity.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedHornTargetIdentity.lean)|
|追加|2026-10-17T11:23:20+09:00 · `8f460a197d13`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedHornTargetIdentity.loop`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetIdentity.evaluation`<br>`SerrePositivity.SimplicialModel.NormalizedHornTargetIdentity.evaluation_reindex`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The previously selected identity comparison bounds a relative constant-edge triangle。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0505"></a>

### m0505 · HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn

|項目|記録|
|---|---|
|分類|B|
|ソース|[NormalizedTriangleHorn.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/NormalizedTriangleHorn.lean)|
|追加|2026-10-17T10:52:25+09:00 · `880c661b5d70`|
|主な公開宣言|`SerrePositivity.SimplicialModel.NormalizedTriangleHorn.compatible`<br>`SerrePositivity.SimplicialModel.NormalizedTriangleHorn.fill_restriction`<br>`SerrePositivity.SimplicialModel.NormalizedTriangleHorn.family_degeneracy`|
|直接import元|[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One triangle horn filling operation preserves both degeneracies simultaneously。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0506"></a>

### m0506 · HomotopicalAlgebra.Simplicial.OppositeHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[OppositeHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/OppositeHomotopy.lean)|
|追加|2026-10-17T09:16:00+09:00 · `b445024cc0df`|
|主な公開宣言|`SerrePositivity.SimplicialModel.OppositeHomotopy.localized_reversed_augmentation_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.OppositeHomotopy.localized_reversed_augmentation_isIso` — 単体方向を反転したaugmentationも指定された条件のもとで局所化可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0507"></a>

### m0507 · HomotopicalAlgebra.Simplicial.ParameterCategory

|項目|記録|
|---|---|
|分類|C|
|ソース|[ParameterCategory.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ParameterCategory.lean)|
|追加|2026-10-17T04:26:51+09:00 · `e7f3364653ce`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ParameterCategory.Object`<br>`SerrePositivity.SimplicialModel.ParameterCategory.reindex_id`<br>`SerrePositivity.SimplicialModel.ParameterCategory.reindex_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedChoices](#m0166)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|一般のパラメータ付き射の圏にも見えるが、移動パラメータの厳密化に合わせたAPIである。|
|現状の構成|Categories of maps with a shared arbitrary simplicial parameter。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0508"></a>

### m0508 · HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[ParameterChoiceDiagram.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ParameterChoiceDiagram.lean)|
|追加|2026-10-17T10:03:40+09:00 · `e455b341e062`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ParameterChoiceDiagram.target`<br>`SerrePositivity.SimplicialModel.ParameterChoiceDiagram.point_app`<br>`SerrePositivity.SimplicialModel.ParameterChoiceDiagram.point_projection`|
|直接import元|[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict small diagram of relative choices over all restrictions of a parameter。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0509"></a>

### m0509 · HomotopicalAlgebra.Simplicial.ParameterComposition

|項目|記録|
|---|---|
|分類|C|
|ソース|[ParameterComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ParameterComposition.lean)|
|追加|2026-10-17T04:13:32+09:00 · `09e54ad25ec0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ParameterComposition.comp`<br>`SerrePositivity.SimplicialModel.ParameterComposition.substitute_const`<br>`SerrePositivity.SimplicialModel.ParameterComposition.simplex_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterComposition](#m0361)<br>[HomotopicalAlgebra.Simplicial.ParameterCategory](#m0507)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies](#m0537)<br>[HomotopicalAlgebra.Simplicial.RetractChainFamily](#m0547)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies](#m0171)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition](#m0360)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterComposition](#m0361)<br>[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)<br>[HomotopicalAlgebra.Simplicial.ParameterCategory](#m0507)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies](#m0537)<br>[HomotopicalAlgebra.Simplicial.RetractChainFamily](#m0547)<br>[HomotopicalAlgebra.Simplicial.RetractChainUnits](#m0548)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|パラメータ付き合成は再利用候補だが、現行の厳密化用インターフェースから独立していない。|
|現状の構成|Composition with one arbitrary shared simplicial parameter。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0510"></a>

### m0510 · HomotopicalAlgebra.Simplicial.ParameterCube

|項目|記録|
|---|---|
|分類|A|
|ソース|[ParameterCube.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ParameterCube.lean)|
|追加|2026-10-17T04:13:32+09:00 · `09e54ad25ec0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ParameterCube.face_coordinate_same`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.Simplicial.WordSegment](#m0617)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ParameterCube.face_coordinate_same` — 単体的区間の有限直積の座標面が指定した座標に一致する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0511"></a>

### m0511 · HomotopicalAlgebra.Simplicial.ParameterizedHornChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[ParameterizedHornChoices.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ParameterizedHornChoices.lean)|
|追加|2026-10-17T10:33:30+09:00 · `ff6318d37ef6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ParameterizedHornChoices.obj`<br>`SerrePositivity.SimplicialModel.ParameterizedHornChoices.relative_extension`<br>`SerrePositivity.SimplicialModel.ParameterizedHornChoices.fixedFacesComparison`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.KanHornFamilyLifting](#m0415)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanHornFamilyLifting](#m0415)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative choices of whole horn fillers in every dimension。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0512"></a>

### m0512 · HomotopicalAlgebra.Simplicial.PiZeroConstant

|項目|記録|
|---|---|
|分類|A|
|ソース|[PiZeroConstant.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/PiZeroConstant.lean)|
|追加|2026-10-17T02:58:23+09:00 · `b89d729dcc44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.PiZeroConstant.homotopy_eq`<br>`SerrePositivity.SimplicialModel.PiZeroConstant.homEquiv`|
|直接import元|[HomotopicalAlgebra.Simplicial.DiscreteFiber](#m0393)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamily](#m0391)<br>[HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting](#m0392)<br>[HomotopicalAlgebra.Simplicial.DiscreteFiber](#m0393)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)<br>[HomotopicalAlgebra.Simplicial.PiZeroLocalization](#m0513)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.PiZeroConstant.homotopy_eq` — 離散単体的集合を値とするホモトピックな二射は等しい。|
|入口の主張|`SerrePositivity.SimplicialModel.PiZeroConstant.homEquiv` — 離散単体的集合への写像と連結成分からの関数との全単射を構成する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0513"></a>

### m0513 · HomotopicalAlgebra.Simplicial.PiZeroLocalization

|項目|記録|
|---|---|
|分類|A|
|ソース|[PiZeroLocalization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/PiZeroLocalization.lean)|
|追加|2026-10-17T02:58:23+09:00 · `b89d729dcc44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.PiZeroLocalization.piZero_bijective`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses](#m0248)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.Simplicial.DiscreteKanExtension](#m0394)<br>[HomotopicalAlgebra.Simplicial.DiscreteLocalizedExtension](#m0395)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.PiZeroLocalization.piZero_bijective` — anodyne局所化で可逆な射は実際の連結成分の全単射を誘導する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0514"></a>

### m0514 · HomotopicalAlgebra.Simplicial.PrecompositionHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[PrecompositionHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/PrecompositionHomotopy.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.PrecompositionHomotopy.homotopy`|
|直接import元|[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.MappingPrecompositionRetraction](#m0450)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.PrecompositionHomotopy.homotopy` — 指定した実区間ホモトピーを内部Homへの前合成に移す。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0515"></a>

### m0515 · HomotopicalAlgebra.Simplicial.ProductBoundaryCotensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[ProductBoundaryCotensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ProductBoundaryCotensor.lean)|
|追加|2026-10-16T17:18:29+09:00 · `da71d1d985f6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ProductBoundaryCotensor.standardDesc`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedBoundary](#m0313)<br>[HomotopicalAlgebra.Simplicial.NerveMovingBoundary](#m0480)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ProductBoundaryCotensor.standardDesc` — 追加の動くパラメータを持つ余テンソルの全面を単体境界上に貼り合わせる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0516"></a>

### m0516 · HomotopicalAlgebra.Simplicial.PushoutCotensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[PushoutCotensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/PushoutCotensor.lean)|
|追加|2026-10-16T15:46:16+09:00 · `9d61c8af5c20`|
|主な公開宣言|`SerrePositivity.SimplicialModel.PushoutCotensor.glue`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback](#m0517)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NervePushoutBoundary](#m0491)<br>[HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback](#m0517)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.PushoutCotensor.glue` — 実際のpushoutの二つの脚に沿って互換な余テンソル族を貼り合わせる。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0517"></a>

### m0517 · HomotopicalAlgebra.Simplicial.PushoutInternalHomPullback

|項目|記録|
|---|---|
|分類|A|
|ソース|[PushoutInternalHomPullback.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/PushoutInternalHomPullback.lean)|
|追加|2026-10-17T00:56:21+09:00 · `bd38b6c71550`|
|主な公開宣言|`SerrePositivity.SimplicialModel.PushoutInternalHomPullback.isPullback`|
|直接import元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence](#m0454)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.PushoutInternalHomPullback.isPullback` — 内部Homは元のpushoutを実際のpullbackへ移す。|
|今後の用途|今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。|

<a id="m0518"></a>

### m0518 · HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension

|項目|記録|
|---|---|
|分類|B|
|ソース|[RecursiveChoiceExtension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RecursiveChoiceExtension.lean)|
|追加|2026-10-16T10:49:09+09:00 · `fe7468c4b2dc`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RecursiveChoiceExtension.filtration`<br>`SerrePositivity.SimplicialModel.RecursiveChoiceExtension.family_prescribed`<br>`SerrePositivity.SimplicialModel.RecursiveChoiceExtension.fixed_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Recursive extension of prescribed coherent families。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0519"></a>

### m0519 · HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarAnodyneComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarAnodyneComparison.lean)|
|追加|2026-10-16T19:20:01+09:00 · `42d73f5277b5`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.spanLeftAnodyneIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarAnodyneComparison](#m0269)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.spanLeftAnodyneIso` — 相対bar比較spanの左脚がanodyne局所化後に実際の自然同型となる。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0520"></a>

### m0520 · HomotopicalAlgebra.Simplicial.RelativeBarAugmentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarAugmentation.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.relativeAugmentation`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate](#m0270)<br>[HomotopicalAlgebra.Simplicial.RelativeBarUnit](#m0533)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)<br>[HomotopicalAlgebra.Simplicial.RelativeBarUnit](#m0533)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.relativeAugmentation` — 実際の比較図式上の相対barに自然なaugmentationを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0521"></a>

### m0521 · HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarCommaPresentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarCommaPresentation.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.commaPresentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.commaPresentation` — 相対barを実際の基底comma圏上のbarとして表示する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0522"></a>

### m0522 · HomotopicalAlgebra.Simplicial.RelativeBarConstruction

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarConstruction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarConstruction.lean)|
|追加|2026-10-16T18:49:40+09:00 · `4ff11f4e7d44`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.relative`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCenters](#m0136)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarCenters](#m0288)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAugmentation](#m0520)<br>[HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation](#m0521)<br>[HomotopicalAlgebra.Simplicial.RelativeBarReindex](#m0527)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSections](#m0530)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSimplexCone](#m0218)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate](#m0270)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowPresentations](#m0297)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarSimplexCone](#m0298)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAugmentation](#m0520)<br>[HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation](#m0521)<br>[HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators](#m0523)<br>[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)<br>[HomotopicalAlgebra.Simplicial.RelativeBarReindex](#m0527)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSections](#m0530)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)<br>[HomotopicalAlgebra.Simplicial.RelativeBarUnit](#m0533)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.relative` — 基底圏上で厳密に関手的な相対barをモデル構造なしで構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0523"></a>

### m0523 · HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarContractionOperators.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarContractionOperators.lean)|
|追加|2026-10-16T19:10:22+09:00 · `1a0688723145`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.contractionInterval_operator`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.contractionInterval_operator` — 恒等barの収縮区間が全単体作用素と整合する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0524"></a>

### m0524 · HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarDiagonalContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarDiagonalContraction.lean)|
|追加|2026-10-16T19:10:22+09:00 · `1a0688723145`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.identityDiagonalHomotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.identityDiagonalHomotopy` — 恒等射影のbarの対角に一つの実単体的収縮を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0525"></a>

### m0525 · HomotopicalAlgebra.Simplicial.RelativeBarIdentity

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarIdentity.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarIdentity.lean)|
|追加|2026-10-16T19:00:46+09:00 · `8f58d0eb8b63`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.identityNerveHomotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators](#m0523)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators](#m0523)<br>[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.identityNerveHomotopy` — 恒等射影barのaugmentationの切断とnerveホモトピーを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0526"></a>

### m0526 · HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarMiddleReindex.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarMiddleReindex.lean)|
|追加|2026-10-16T22:54:15+09:00 · `72407006ad64`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.middleReindexImageIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.middleReindexImageIso` — 相対barの中間対象の添字変更が局所化後に同型を与える。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0527"></a>

### m0527 · HomotopicalAlgebra.Simplicial.RelativeBarReindex

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarReindex.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarReindex.lean)|
|追加|2026-10-16T22:46:13+09:00 · `cd8952ad92b3`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.reindex`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.reindex` — 添字変更から相対barの実際の写像を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0528"></a>

### m0528 · HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarSectionHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarSectionHomotopy.lean)|
|追加|2026-10-16T22:09:27+09:00 · `465bb6792c0f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.commaSectionHomotopy`|
|直接import元|[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.commaSectionHomotopy` — 実際のcomma射からbarの全次数に整合するホモトピーを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0529"></a>

### m0529 · HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarSectionUnit.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarSectionUnit.lean)|
|追加|2026-10-16T22:09:27+09:00 · `465bb6792c0f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.spanRight_isIso_iff_section`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.spanRight_isIso_iff_section` — bar比較spanの右脚の可逆性をその源section上の可逆性へ帰着する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0530"></a>

### m0530 · HomotopicalAlgebra.Simplicial.RelativeBarSections

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarSections.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarSections.lean)|
|追加|2026-10-16T22:09:27+09:00 · `465bb6792c0f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.sectionInterval_operator`|
|直接import元|[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.sectionInterval_operator` — 相対barへのsectionの区間が全単体作用素と整合する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0531"></a>

### m0531 · HomotopicalAlgebra.Simplicial.RelativeBarSpan

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarSpan.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarSpan.lean)|
|追加|2026-10-16T19:00:46+09:00 · `8f58d0eb8b63`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.spanSection_retract`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBar](#m0253)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionBarReduction](#m0254)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan](#m0271)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison](#m0519)<br>[HomotopicalAlgebra.Simplicial.RelativeBarMiddleReindex](#m0526)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionUnit](#m0529)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.spanSection_retract` — 相対bar比較spanのsectionが元のaugmentationのレトラクションを与える。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0532"></a>

### m0532 · HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarSpanContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarSpanContraction.lean)|
|追加|2026-10-16T19:10:22+09:00 · `1a0688723145`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.spanLeftHomotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison](#m0519)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction](#m0272)<br>[HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison](#m0519)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.spanLeftHomotopy` — 相対bar比較spanの左脚を収縮する実ホモトピーを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0533"></a>

### m0533 · HomotopicalAlgebra.Simplicial.RelativeBarUnit

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeBarUnit.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBarUnit.lean)|
|追加|2026-10-16T19:00:46+09:00 · `8f58d0eb8b63`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.unit`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarDiagonalContraction](#m0524)<br>[HomotopicalAlgebra.Simplicial.RelativeBarIdentity](#m0525)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.unit` — 恒等射影のbarを介して相対barへの自然な単位を構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0534"></a>

### m0534 · HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeBoundaryFilling.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeBoundaryFilling.lean)|
|追加|2026-10-17T11:19:42+09:00 · `0ae03e32f400`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeBoundaryFilling.boundary_compatible`<br>`SerrePositivity.SimplicialModel.RelativeBoundaryFilling.family`<br>`SerrePositivity.SimplicialModel.RelativeBoundaryFilling.family_reindex`|
|直接import元|[HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle](#m0542)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetAssociativity](#m0500)<br>[HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle](#m0542)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Fill a whole compatible boundary over a fixed base, relative to fixed inputs。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0535"></a>

### m0535 · HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceBoundary.lean)|
|追加|2026-10-16T09:42:54+09:00 · `1ff62113d16f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.fill_faces`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.fill_standard_faces`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.Simplicial.SelectedTriangle](#m0553)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.Simplicial.SelectedTriangle](#m0553)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Filling prescribed compatible faces while retaining a fixed boundary。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0536"></a>

### m0536 · HomotopicalAlgebra.Simplicial.RelativeChoiceCells

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceCells.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceCells.lean)|
|追加|2026-10-16T10:59:10+09:00 · `0592c60b309c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceCells.rule`<br>`SerrePositivity.SimplicialModel.RelativeChoiceCells.family_initial`<br>`SerrePositivity.SimplicialModel.RelativeChoiceCells.fixed_boundary`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Cell-filling rules supplied by the actual relative choice space。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0537"></a>

### m0537 · HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceFamilies.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceFamilies.lean)|
|追加|2026-10-17T04:19:50+09:00 · `47c0de8ad7ff`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_boundary_const`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.familyEquiv`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofFamily_naturality`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The universal property of actual relative extension families。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0538"></a>

### m0538 · HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceFunctor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceFunctor.lean)|
|追加|2026-10-16T13:15:34+09:00 · `f975a2117df0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceFunctor.boundary_naturality`<br>`SerrePositivity.SimplicialModel.RelativeChoiceFunctor.point`<br>`SerrePositivity.SimplicialModel.RelativeChoiceFunctor.point_projection`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram](#m0508)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram](#m0508)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Relative choice spaces in a strict diagram。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0539"></a>

### m0539 · HomotopicalAlgebra.Simplicial.RelativeChoiceIso

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceIso.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceIso.lean)|
|追加|2026-10-16T13:34:33+09:00 · `1972260f2353`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.boundary_inv`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_postIso_inv`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.postIso_ofExtension`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Isomorphisms of actual relative choice spaces。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0540"></a>

### m0540 · HomotopicalAlgebra.Simplicial.RelativeChoiceMaps

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceMaps.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceMaps.lean)|
|追加|2026-10-16T09:54:18+09:00 · `0c8eb6c83508`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.ofExtension_congr`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.preMap_ofExtension`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.family_preMap`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor](#m0538)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceIso](#m0539)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostPoints](#m0054)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.Simplicial.ComparisonCoherenceRestriction](#m0364)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport](#m0371)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornInput](#m0377)<br>[HomotopicalAlgebra.Simplicial.DegenerateTriangleOverlap](#m0379)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram](#m0508)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor](#m0538)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceIso](#m0539)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual transport maps between fixed-boundary comparison spaces。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0541"></a>

### m0541 · HomotopicalAlgebra.Simplicial.RelativeChoiceSpace

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeChoiceSpace.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeChoiceSpace.lean)|
|追加|2026-10-16T09:33:29+09:00 · `dfe2314dbf6e`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.pointUnitIso`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.relative_homotopy`<br>`SerrePositivity.SimplicialModel.RelativeChoiceSpace.nonempty_fixedBoundaryHomotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints](#m0341)<br>[HomotopicalAlgebra.Simplicial.BoundaryCotensor](#m0352)<br>[HomotopicalAlgebra.Simplicial.BoundaryOneCotensor](#m0355)<br>[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension](#m0518)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary](#m0535)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceCells](#m0536)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies](#m0537)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceMaps](#m0540)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy](#m0594)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedTransport](#m0052)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction](#m0057)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftEdges](#m0065)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftFaces](#m0066)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.FramedPreChoiceFunctor](#m0089)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentIntervals](#m0114)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCoherentTriangles](#m0115)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceFunctor](#m0117)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceCategory](#m0140)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceComposition](#m0142)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace](#m0143)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionAction](#m0178)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChoiceFunctor](#m0259)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallAction](#m0325)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints](#m0341)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)<br>[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice](#m0444)<br>[HomotopicalAlgebra.Simplicial.LocalizedRelativeChoice](#m0449)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterMapLaws](#m0462)<br>[HomotopicalAlgebra.Simplicial.NerveBoundaryExtension](#m0464)<br>[HomotopicalAlgebra.Simplicial.NerveEvaluationLaws](#m0471)<br>[HomotopicalAlgebra.Simplicial.NerveIntervalBoundary](#m0475)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveNaturalBoundary](#m0485)<br>[HomotopicalAlgebra.Simplicial.NerveParameterExtension](#m0487)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTetrahedron](#m0496)<br>[HomotopicalAlgebra.Simplicial.NormalizedComparisonTriangle](#m0497)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.ParameterChoiceDiagram](#m0508)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)<br>[HomotopicalAlgebra.Simplicial.RecursiveChoiceExtension](#m0518)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceBoundary](#m0535)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceCells](#m0536)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFamilies](#m0537)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceFunctor](#m0538)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceIso](#m0539)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceMaps](#m0540)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation](#m0546)<br>[HomotopicalAlgebra.Simplicial.SelectedLoopContraction](#m0552)<br>[HomotopicalAlgebra.Simplicial.SelectedTriangle](#m0553)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy](#m0594)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual spaces of extensions with a fixed simplicial boundary。自明fibrationのファイバーと相対延長による選択の比較に対応する足場。|

<a id="m0542"></a>

### m0542 · HomotopicalAlgebra.Simplicial.RelativeComparisonTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeComparisonTriangle.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeComparisonTriangle.lean)|
|追加|2026-10-17T11:19:42+09:00 · `0ae03e32f400`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeComparisonTriangle.faces`<br>`SerrePositivity.SimplicialModel.RelativeComparisonTriangle.triangle_base`<br>`SerrePositivity.SimplicialModel.RelativeComparisonTriangle.triangle_relative`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition](#m0502)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornTargetIdentity](#m0504)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A relative triangle retains all three previously selected comparison edges。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0543"></a>

### m0543 · HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation

|項目|記録|
|---|---|
|分類|B|
|ソース|[RelativeHornFillingOperation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeHornFillingOperation.lean)|
|追加|2026-10-17T10:44:23+09:00 · `64adc4f99794`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeHornFillingOperation.section_`<br>`SerrePositivity.SimplicialModel.RelativeHornFillingOperation.family_naturality`<br>`SerrePositivity.SimplicialModel.RelativeHornFillingOperation.family_prescribed`|
|直接import元|[HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation](#m0372)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornInput](#m0377)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CompatibleHornFillingOperation](#m0372)<br>[HomotopicalAlgebra.Simplicial.DegenerateHornInput](#m0377)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|One uniform horn filling operation preserves an entire prescribed input family。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0544"></a>

### m0544 · HomotopicalAlgebra.Simplicial.RelativeProductLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[RelativeProductLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeProductLifting.lean)|
|追加|2026-10-17T11:19:42+09:00 · `0ae03e32f400`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeProductLifting.exists_lift`<br>`SerrePositivity.SimplicialModel.RelativeProductLifting.lift`|
|直接import元|[HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling](#m0534)<br>[HomotopicalAlgebra.Simplicial.RelativeFillerComparison](../SerrePositivity/HomotopicalAlgebra/Simplicial/RelativeFillerComparison.lean)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBoundaryFilling](#m0534)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.RelativeProductLifting.exists_lift` — 二つの単射のpushout-productから以前の族と指定部分と基底を同時に保つ持ち上げを構成する。|
|入口の主張|`SerrePositivity.SimplicialModel.RelativeProductLifting.lift` — 以前の族と指定部分と基底を保持する一つの実際の持ち上げを選ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0545"></a>

### m0545 · HomotopicalAlgebra.Simplicial.RestrictionDescentChoices

|項目|記録|
|---|---|
|分類|B|
|ソース|[RestrictionDescentChoices.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RestrictionDescentChoices.lean)|
|追加|2026-10-17T09:35:05+09:00 · `6ac6247d8399`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RestrictionDescentChoices.restriction`<br>`SerrePositivity.SimplicialModel.RestrictionDescentChoices.familyComparison`<br>`SerrePositivity.SimplicialModel.RestrictionDescentChoices.relative_extension`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation](#m0546)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation](#m0546)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual spaces of descent choices with relative parameter extension。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0546"></a>

### m0546 · HomotopicalAlgebra.Simplicial.RestrictionDescentEvaluation

|項目|記録|
|---|---|
|分類|B|
|ソース|[RestrictionDescentEvaluation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RestrictionDescentEvaluation.lean)|
|追加|2026-10-17T09:37:24+09:00 · `146b97395294`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RestrictionDescentChoices.constant_name_family`<br>`SerrePositivity.SimplicialModel.RestrictionDescentChoices.fixedFamilyComparison`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The comparison family restricts to the original map over the whole parameter。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0547"></a>

### m0547 · HomotopicalAlgebra.Simplicial.RetractChainFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractChainFamily.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RetractChainFamily.lean)|
|追加|2026-10-17T04:13:32+09:00 · `09e54ad25ec0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RetractChainFamily.interval`<br>`SerrePositivity.SimplicialModel.RetractChainFamily.transfer_last_parameter`<br>`SerrePositivity.SimplicialModel.RetractChainFamily.one_face`|
|直接import元|[HomotopicalAlgebra.Simplicial.ParameterCube](#m0510)<br>[HomotopicalAlgebra.Simplicial.RetractChainUnits](#m0548)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainTransfer](#m0173)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.Simplicial.ParameterCube](#m0510)<br>[HomotopicalAlgebra.Simplicial.RetractChainUnits](#m0548)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)<br>[HomotopicalAlgebra.Simplicial.WordSegment](#m0617)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All finite chains with independently prescribed contraction parameters。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0548"></a>

### m0548 · HomotopicalAlgebra.Simplicial.RetractChainUnits

|項目|記録|
|---|---|
|分類|B|
|ソース|[RetractChainUnits.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RetractChainUnits.lean)|
|追加|2026-10-17T07:08:24+09:00 · `34545b1cf321`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RetractChainUnits.contraction_over`<br>`SerrePositivity.SimplicialModel.RetractChainUnits.interior_identity_after_zero`<br>`SerrePositivity.SimplicialModel.RetractChainUnits.interior_identity_at_zero`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Endpoint unit laws and absorbing contraction parameters for retract chains。bar型の鎖パラメータと整合図式の厳密化に対応する足場。|

<a id="m0549"></a>

### m0549 · HomotopicalAlgebra.Simplicial.RetractEndomorphisms

|項目|記録|
|---|---|
|分類|C|
|ソース|[RetractEndomorphisms.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/RetractEndomorphisms.lean)|
|追加|2026-10-17T07:25:19+09:00 · `2efc3cce9602`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RetractEndomorphisms.End`<br>`SerrePositivity.SimplicialModel.RetractEndomorphisms.mul_apply`<br>`SerrePositivity.SimplicialModel.RetractEndomorphisms.word_intertwining`|
|直接import元|[HomotopicalAlgebra.Simplicial.WordRetractionAction](#m0616)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)<br>[HomotopicalAlgebra.Simplicial.WordRetractionAction](#m0616)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|split retractionの自己射は一般的だが、現状の用途はword作用である。|
|現状の構成|Endomorphisms over a split retraction and under its section。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0550"></a>

### m0550 · HomotopicalAlgebra.Simplicial.ReversedSimplexParameters

|項目|記録|
|---|---|
|分類|A|
|ソース|[ReversedSimplexParameters.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/ReversedSimplexParameters.lean)|
|追加|2026-10-17T06:33:20+09:00 · `9e6b5af1fc1f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.ReversedSimplexParameters.delta_sigma_self`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegenerateBoundary](#m0183)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionMixedFaces](#m0185)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.ReversedSimplexParameters.delta_sigma_self` — 向きを反転した単体パラメータの面と退化の対応する恒等式を証明する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0551"></a>

### m0551 · HomotopicalAlgebra.Simplicial.SegmentWords

|項目|記録|
|---|---|
|分類|B|
|ソース|[SegmentWords.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SegmentWords.lean)|
|追加|2026-10-17T07:17:56+09:00 · `1f744bb07092`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SegmentWords.Word`<br>`SerrePositivity.SimplicialModel.SegmentWords.map_id`<br>`SerrePositivity.SimplicialModel.SegmentWords.map_comp`|
|直接import元|[HomotopicalAlgebra.Simplicial.RetractEndomorphisms](#m0549)<br>[HomotopicalAlgebra.Simplicial.WordSegment](#m0617)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RetractEndomorphisms](#m0549)<br>[HomotopicalAlgebra.Simplicial.WordRetractionAction](#m0616)<br>[HomotopicalAlgebra.Simplicial.WordSegment](#m0617)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Finite words with a unit endpoint and an absorbing endpoint。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0552"></a>

### m0552 · HomotopicalAlgebra.Simplicial.SelectedLoopContraction

|項目|記録|
|---|---|
|分類|B|
|ソース|[SelectedLoopContraction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SelectedLoopContraction.lean)|
|追加|2026-10-16T10:41:12+09:00 · `a6a9a53c32f4`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SelectedLoopContraction.degenerate`<br>`SerrePositivity.SimplicialModel.SelectedLoopContraction.fill`<br>`SerrePositivity.SimplicialModel.SelectedLoopContraction.fill_face`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Contracting a selected loop without replacing its edge。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0553"></a>

### m0553 · HomotopicalAlgebra.Simplicial.SelectedTriangle

|項目|記録|
|---|---|
|分類|B|
|ソース|[SelectedTriangle.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SelectedTriangle.lean)|
|追加|2026-10-16T10:26:43+09:00 · `270ce23f6d34`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SelectedTriangle.Boundary`<br>`SerrePositivity.SimplicialModel.SelectedTriangle.fill_face`<br>`SerrePositivity.SimplicialModel.SelectedTriangle.fill_fixed_boundary`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.SelectedLoopContraction](#m0552)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedComparison](#m0067)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitComparison](#m0073)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.MixedChoiceCompatibility](#m0116)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.SelectedLoopContraction](#m0552)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Filling a triangle from its specified edges and endpoints。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0554"></a>

### m0554 · HomotopicalAlgebra.Simplicial.SequentialBoundaryFactorization

|項目|記録|
|---|---|
|分類|A|
|ソース|[SequentialBoundaryFactorization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SequentialBoundaryFactorization.lean)|
|追加|2026-10-17T01:13:22+09:00 · `1fe081476cdf`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SequentialBoundaryFactorization.relative_mono`|
|直接import元|[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLift](#m0555)<br>[HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses](#m0556)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SequentialBoundaryFactorization.relative_mono` — 逐次図式の境界分解で相対的な後続比較射が単射となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0555"></a>

### m0555 · HomotopicalAlgebra.Simplicial.SequentialFactorLift

|項目|記録|
|---|---|
|分類|A|
|ソース|[SequentialFactorLift.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SequentialFactorLift.lean)|
|追加|2026-10-17T01:13:22+09:00 · `1fe081476cdf`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SequentialFactorLift.hasLiftingProperty`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SequentialFactorLift.hasLiftingProperty` — 既存の段階を保持する逐次持ち上げから全体の持ち上げ性を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0556"></a>

### m0556 · HomotopicalAlgebra.Simplicial.SequentialFactorLiftingClasses

|項目|記録|
|---|---|
|分類|A|
|ソース|[SequentialFactorLiftingClasses.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SequentialFactorLiftingClasses.lean)|
|追加|2026-10-17T01:13:22+09:00 · `1fe081476cdf`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses.relative_llp`|
|直接import元|[HomotopicalAlgebra.Simplicial.SequentialFactorLift](#m0555)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanSequentialColimitComparison](#m0436)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SequentialFactorLiftingClasses.relative_llp` — 逐次比較の相対後続因子が指定した左持ち上げクラスに属する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0557"></a>

### m0557 · HomotopicalAlgebra.Simplicial.SimplexIndexFinite

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexIndexFinite.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexIndexFinite.lean)|
|追加|2026-10-16T13:49:39+09:00 · `c5b8792f501b`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexIndexFinite.map_inverse_injective`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)<br>[HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal](#m0560)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)<br>[HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary](#m0559)<br>[HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal](#m0560)<br>[HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting](#m0561)<br>[HomotopicalAlgebra.Simplicial.SimplexNaturalMatching](#m0562)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexIndexFinite.map_inverse_injective` — 単体圏の逆射が誘導する単体的集合の写像は単射となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0558"></a>

### m0558 · HomotopicalAlgebra.Simplicial.SimplexInverseMatching

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexInverseMatching.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexInverseMatching.lean)|
|追加|2026-10-16T14:08:11+09:00 · `4dca7af70c9c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexInverseMatching.reedyRight`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveCoherentExtension](#m0465)<br>[HomotopicalAlgebra.Simplicial.SimplexNaturalMatching](#m0562)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveCoherentExtension](#m0465)<br>[HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting](#m0561)<br>[HomotopicalAlgebra.Simplicial.SimplexNaturalMatching](#m0562)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexInverseMatching.reedyRight` — 退化を可逆にする図式のmatching条件からReedy右クラスへの所属を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0559"></a>

### m0559 · HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexLatchingBoundary.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexLatchingBoundary.lean)|
|追加|2026-10-16T13:58:49+09:00 · `95d8d9bbb600`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexLatchingBoundary.boundaryArrowIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveCoherentExtension](#m0465)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexLatchingBoundary.boundaryArrowIso` — 単体圏上のパラメータ図式のlatching射を実際の単体境界射と同型で結ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0560"></a>

### m0560 · HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexMatchingTerminal.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexMatchingTerminal.lean)|
|追加|2026-10-16T14:08:11+09:00 · `4dca7af70c9c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexMatchingTerminal.matchingComparison_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)<br>[HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting](#m0561)<br>[HomotopicalAlgebra.Simplicial.SimplexNaturalMatching](#m0562)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexMatchingTerminal.matchingComparison_isIso` — 逆境界が非空な場合に非退化核を使ってmatching比較の同型性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0561"></a>

### m0561 · HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexMonomorphismLifting.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexMonomorphismLifting.lean)|
|追加|2026-10-16T14:58:04+09:00 · `03f095fac8a0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexMonomorphismLifting.relativeMatching_rightLifting`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveDiagramExtension](#m0470)<br>[HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting](#m0479)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexMonomorphismLifting.relativeMatching_rightLifting` — 各成分のすべての単射に対する右持ち上げ性から相対matching射の右持ち上げ性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0562"></a>

### m0562 · HomotopicalAlgebra.Simplicial.SimplexNaturalMatching

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNaturalMatching.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNaturalMatching.lean)|
|追加|2026-10-16T14:31:18+09:00 · `3d6feb1b6039`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNaturalMatching.reedyRight`|
|直接import元|[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)<br>[HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting](#m0561)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.NerveRelativeValueExtension](#m0493)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNaturalMatching.reedyRight` — 退化を可逆にする図式間の各点自明fibrationからReedy右クラスへの所属を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0563"></a>

### m0563 · HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNerveAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNerveAugmentation.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNerveAugmentation.augmentation`|
|直接import元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveFunctor](#m0565)|
|宣言参照元|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge](#m0201)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveFunctor](#m0565)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerveAugmentation.augmentation` — 単体圏のnerveから元の単体的集合への自然なaugmentationを構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0564"></a>

### m0564 · HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNerveEquivalence.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNerveEquivalence.lean)|
|追加|2026-10-17T01:20:19+09:00 · `bb54cd3df030`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNerve.augmentation_localized_isIso`<br>`SerrePositivity.SimplicialModel.SimplexNerve.augmentation_image_isIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerve.augmentation_localized_isIso` — 任意の単体的集合について単体圏nerveのaugmentationは局所化で可逆となる。|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerve.augmentation_image_isIso` — anodyne射を反転する任意の関手は単体圏nerveのaugmentationを同型へ送る。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0565"></a>

### m0565 · HomotopicalAlgebra.Simplicial.SimplexNerveFunctor

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNerveFunctor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNerveFunctor.lean)|
|追加|2026-10-16T23:46:40+09:00 · `3d22bdf25143`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNerve.degreeSumIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexNerveMonos](#m0566)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveMonos](#m0566)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveStandard](#m0567)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerve.degreeSumIso` — 単体圏nerveの各次数を次数ごとのラベルによる直和として表す同型を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0566"></a>

### m0566 · HomotopicalAlgebra.Simplicial.SimplexNerveMonos

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNerveMonos.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNerveMonos.lean)|
|追加|2026-10-16T23:46:40+09:00 · `3d22bdf25143`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNerve.map_injective`|
|直接import元|[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveStandard](#m0567)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerve.map_injective` — 単体圏のnerveを取る関手は単射を保つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0567"></a>

### m0567 · HomotopicalAlgebra.Simplicial.SimplexNerveStandard

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexNerveStandard.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexNerveStandard.lean)|
|追加|2026-10-16T23:46:40+09:00 · `3d22bdf25143`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexNerve.standardAugmentation_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence](#m0564)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexNerve.standardAugmentation_isIso` — 標準単体に対する単体圏nerveのaugmentationは指定局所化で可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0568"></a>

### m0568 · HomotopicalAlgebra.Simplicial.SimplexParameterHom

|項目|記録|
|---|---|
|分類|A|
|ソース|[SimplexParameterHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SimplexParameterHom.lean)|
|追加|2026-10-17T03:40:33+09:00 · `db5028c13bfe`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SimplexParameterHom.native_kan`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)<br>[HomotopicalAlgebra.Simplicial.ParameterComposition](#m0509)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom](#m0600)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleChoices](#m0367)<br>[HomotopicalAlgebra.Simplicial.ComparisonTriangleParameterDiagram](#m0370)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTetrahedron](#m0408)<br>[HomotopicalAlgebra.Simplicial.KanComparisonTriangle](#m0409)<br>[HomotopicalAlgebra.Simplicial.KanRestrictionEquivalence](#m0433)<br>[HomotopicalAlgebra.Simplicial.NormalizedHornFilling](#m0498)<br>[HomotopicalAlgebra.Simplicial.ParameterComposition](#m0509)<br>[HomotopicalAlgebra.Simplicial.ParameterizedHornChoices](#m0511)<br>[HomotopicalAlgebra.Simplicial.RestrictionDescentChoices](#m0545)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry](#m0591)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom](#m0600)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SimplexParameterHom.native_kan` — Kan値の全単体パラメータ写像空間はKan複体となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0569"></a>

### m0569 · HomotopicalAlgebra.Simplicial.SkeletalCellGluing

|項目|記録|
|---|---|
|分類|A|
|ソース|[SkeletalCellGluing.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SkeletalCellGluing.lean)|
|追加|2026-10-16T10:59:10+09:00 · `0592c60b309c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SkeletalCellGluing.assemble_prescribed`|
|直接import元|[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceCells](#m0536)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.BoundaryFillerLifting](#m0353)<br>[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.RelativeChoiceCells](#m0536)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SkeletalCellGluing.assemble_prescribed` — 非退化単体ごとの指定値を保つ骨格上の写像を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0570"></a>

### m0570 · HomotopicalAlgebra.Simplicial.SkeletalDimension

|項目|記録|
|---|---|
|分類|A|
|ソース|[SkeletalDimension.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SkeletalDimension.lean)|
|追加|2026-10-17T01:20:19+09:00 · `bb54cd3df030`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SkeletalDimension.stageIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.CellularNaturalComparison](#m0359)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SkeletalDimension.stageIso` — 指定した次元範囲で骨格段階を元の単体的集合と同型で結ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0571"></a>

### m0571 · HomotopicalAlgebra.Simplicial.SmallDiagramQuotient

|項目|記録|
|---|---|
|分類|B|
|ソース|[SmallDiagramQuotient.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallDiagramQuotient.lean)|
|追加|2026-10-17T02:25:25+09:00 · `a9ec45e7bd04`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallDiagramQuotient.total_small`<br>`SerrePositivity.SimplicialModel.SmallDiagramQuotient.kan`<br>`SerrePositivity.SimplicialModel.SmallDiagramQuotient.map_weakEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)<br>[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingClasses](#m0199)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A strict small quotient diagram with a natural localized comparison。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0572"></a>

### m0572 · HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex

|項目|記録|
|---|---|
|分類|A|
|ソース|[SmallDominatedSubcomplex.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallDominatedSubcomplex.lean)|
|追加|2026-10-17T02:01:36+09:00 · `af5e0ec787ef`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallDominatedSubcomplex.inclusionImageIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SmallDominatedSubcomplex.inclusionImageIso` — 小さい支配対象から得た部分複体の包含が指定局所化で可逆となる。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0573"></a>

### m0573 · HomotopicalAlgebra.Simplicial.SmallKanHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[SmallKanHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallKanHomotopy.lean)|
|追加|2026-10-17T03:32:15+09:00 · `d9187beee7ad`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallKanHomotopy.Object`<br>`SerrePositivity.SimplicialModel.SmallKanHomotopy.realization`<br>`SerrePositivity.SimplicialModel.SmallKanHomotopy.fullyFaithful`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Small Kan values with small interval-homotopy-class morphisms。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0574"></a>

### m0574 · HomotopicalAlgebra.Simplicial.SmallParameterClosure

|項目|記録|
|---|---|
|分類|B|
|ソース|[SmallParameterClosure.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallParameterClosure.lean)|
|追加|2026-10-17T02:01:36+09:00 · `af5e0ec787ef`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallParameterClosure.IsSmall`<br>`SerrePositivity.SimplicialModel.SmallParameterClosure.closure_small`<br>`SerrePositivity.SimplicialModel.SmallParameterClosure.closed`|
|直接import元|[HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex](#m0572)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex](#m0572)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A small subcomplex closed under a whole simplicial parameter operation。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0575"></a>

### m0575 · HomotopicalAlgebra.Simplicial.SmallSimplicialValue

|項目|記録|
|---|---|
|分類|A|
|ソース|[SmallSimplicialValue.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallSimplicialValue.lean)|
|追加|2026-10-17T02:01:36+09:00 · `af5e0ec787ef`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallSimplicialValue.diagramLiftIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarLabelSurjectivity](#m0198)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SmallSimplicialValue.diagramLiftIso` — 各次数の小ささが証明済みの図式を小さい値宇宙へ移し元のliftと自然同型で結ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0576"></a>

### m0576 · HomotopicalAlgebra.Simplicial.SmallSubdiagramObstruction

|項目|記録|
|---|---|
|分類|B|
|ソース|[SmallSubdiagramObstruction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallSubdiagramObstruction.lean)|
|追加|2026-10-17T02:13:59+09:00 · `3fc5c6030758`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallSubdiagramObstruction.Index`<br>`SerrePositivity.SimplicialModel.SmallSubdiagramObstruction.smallQuotient`<br>`SerrePositivity.SimplicialModel.SmallSubdiagramObstruction.smallQuotient_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient](#m0579)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Objectwise homotopical smallness does not give a small natural subdiagram。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0577"></a>

### m0577 · HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient

|項目|記録|
|---|---|
|分類|B|
|ソース|[SmallTargetKernelQuotient.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SmallTargetKernelQuotient.lean)|
|追加|2026-10-17T03:24:44+09:00 · `9a746c831759`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SmallTargetKernelQuotient.arrows`<br>`SerrePositivity.SimplicialModel.SmallTargetKernelQuotient.kernelComparison_isIso`<br>`SerrePositivity.SimplicialModel.SmallTargetKernelQuotient.quotient_boundary_rlp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual small kernel quotients after an anodyne enlargement。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0578"></a>

### m0578 · HomotopicalAlgebra.Simplicial.SplitLocalizedDescent

|項目|記録|
|---|---|
|分類|A|
|ソース|[SplitLocalizedDescent.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/SplitLocalizedDescent.lean)|
|追加|2026-10-17T09:25:57+09:00 · `87fa0f1fda13`|
|主な公開宣言|`SerrePositivity.SimplicialModel.SplitLocalizedDescent.tensor_descend_homotopy`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.SplitLocalizedDescent.tensor_descend_homotopy` — 分裂した局所化同値に沿うKan値ホモトピーの降下をテンソル付きの族に拡張する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0579"></a>

### m0579 · HomotopicalAlgebra.Simplicial.StarDiagramSmallQuotient

|項目|記録|
|---|---|
|分類|B|
|ソース|[StarDiagramSmallQuotient.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/StarDiagramSmallQuotient.lean)|
|追加|2026-10-17T02:25:25+09:00 · `a9ec45e7bd04`|
|主な公開宣言|`SerrePositivity.SimplicialModel.StarDiagramSmallQuotient.original`<br>`SerrePositivity.SimplicialModel.StarDiagramSmallQuotient.imageIso`<br>`SerrePositivity.SimplicialModel.StarDiagramSmallQuotient.kan`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The congruence construction smallifies the large star by a natural quotient。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0580"></a>

### m0580 · HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample

|項目|記録|
|---|---|
|分類|B|
|ソース|[StrictValueDescentCounterexample.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/StrictValueDescentCounterexample.lean)|
|追加|2026-10-16T18:38:31+09:00 · `21a2851d02b0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.StrictValueObstruction.Base`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.repairComparison_isIso`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.repairComparisonIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample](#m0582)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample](#m0582)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A localized strict diagram with small Kan values that has no fixed-value strict lift。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0581"></a>

### m0581 · HomotopicalAlgebra.Simplicial.StrictValueObstruction

|項目|記録|
|---|---|
|分類|B|
|ソース|[StrictValueObstruction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/StrictValueObstruction.lean)|
|追加|2026-10-16T18:38:31+09:00 · `21a2851d02b0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.StrictValueObstruction.point`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.complex_not_subsingleton_vertices`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.not_iso_point`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample](#m0580)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.StrictValueDescentCounterexample](#m0580)<br>[HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample](#m0582)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Weakly equivalent Kan values can obstruct a strict functor on those fixed values。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0582"></a>

### m0582 · HomotopicalAlgebra.Simplicial.StrictValuePresentationCounterexample

|項目|記録|
|---|---|
|分類|B|
|ソース|[StrictValuePresentationCounterexample.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/StrictValuePresentationCounterexample.lean)|
|追加|2026-10-16T18:38:31+09:00 · `21a2851d02b0`|
|主な公開宣言|`SerrePositivity.SimplicialModel.StrictValueObstruction.Presentations`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.parallel_maps_localize_equal`<br>`SerrePositivity.SimplicialModel.StrictValueObstruction.changedValueComparison_localized_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Full presentation projection and local independence do not force fixed-value descent。整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。|

<a id="m0583"></a>

### m0583 · HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation

|項目|記録|
|---|---|
|分類|A|
|ソース|[TotalNerveBarAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/TotalNerveBarAugmentation.lean)|
|追加|2026-10-16T23:24:33+09:00 · `8f5e8bfe16b6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.BarConstruction.TotalNerve.augmentation`|
|直接import元|[HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation](#m0521)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint](#m0164)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation](#m0521)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.BarConstruction.TotalNerve.augmentation` — 全要素の圏のnerveから対角barへの実際のaugmentationを構成する。|
|今後の用途|今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。|

<a id="m0584"></a>

### m0584 · HomotopicalAlgebra.Simplicial.TriangleBook

|項目|記録|
|---|---|
|分類|C|
|ソース|[TriangleBook.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/TriangleBook.lean)|
|追加|2026-10-16T11:08:26+09:00 · `d612fe0bf80f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.TriangleBook.edges`<br>`SerrePositivity.SimplicialModel.TriangleBook.triangle_desc`<br>`SerrePositivity.SimplicialModel.TriangleBook.sharedEdge_desc`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.Simplicial.TriangleBookMaps](#m0585)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainKanParameter](#m0257)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostChainReindexing](#m0258)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PostCompositionChain](#m0260)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)<br>[HomotopicalAlgebra.Simplicial.TriangleBookMaps](#m0585)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|三角形セルの図式は一般化候補だが、比較の整合性を表す専用形状である。|
|現状の構成|A family of triangles with one shared edge。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0585"></a>

### m0585 · HomotopicalAlgebra.Simplicial.TriangleBookMaps

|項目|記録|
|---|---|
|分類|C|
|ソース|[TriangleBookMaps.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/TriangleBookMaps.lean)|
|追加|2026-10-16T11:15:21+09:00 · `462a22b3c87c`|
|主な公開宣言|`SerrePositivity.SimplicialModel.TriangleBook.hom_ext`<br>`SerrePositivity.SimplicialModel.TriangleBook.reindex_comp`<br>`SerrePositivity.SimplicialModel.TriangleBook.desc_reindex`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AnchoredPostComparison](#m0059)<br>[HomotopicalAlgebra.Simplicial.KanTriangleFamily](#m0439)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|セル形状間の写像は再利用候補だが、TriangleBookの専用インターフェースに依存する。|
|現状の構成|Strict reindexing of triangles with a shared edge。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0586"></a>

### m0586 · HomotopicalAlgebra.Simplicial.TriangleDegeneracyParameters

|項目|記録|
|---|---|
|分類|B|
|ソース|[TriangleDegeneracyParameters.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/TriangleDegeneracyParameters.lean)|
|追加|2026-10-17T05:56:11+09:00 · `f098bda39ab4`|
|主な公開宣言|`SerrePositivity.SimplicialModel.TriangleDegeneracyParameters.interval`<br>`SerrePositivity.SimplicialModel.TriangleDegeneracyParameters.tensor_const_zero`<br>`SerrePositivity.SimplicialModel.TriangleDegeneracyParameters.tensor_const_one`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTriangleDegeneracy](#m0192)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|All six faces of the two degenerate triangle parameters。全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。|

<a id="m0587"></a>

### m0587 · HomotopicalAlgebra.Simplicial.UnderMonoBrown

|項目|記録|
|---|---|
|分類|A|
|ソース|[UnderMonoBrown.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UnderMonoBrown.lean)|
|追加|2026-10-17T00:43:39+09:00 · `012b8e4f5068`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UnderMonoBrown.map_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.KanPushoutComparison](#m0429)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.KanPushoutComparison](#m0429)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UnderMonoBrown.map_isIso` — 単体的集合の下の単射対象にBrownの余積論法を適用して像の可逆性を導く。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0588"></a>

### m0588 · HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftAnodyne.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftAnodyne.lean)|
|追加|2026-10-16T19:28:07+09:00 · `8fd5e26041a7`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.anodyne_map`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence](#m0162)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarMappingComparison](#m0200)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.anodyne_map` — 宇宙liftはモデル構造を仮定せずanodyne射を保つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0589"></a>

### m0589 · HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftAnodyneReflection.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftAnodyneReflection.lean)|
|追加|2026-10-16T19:38:32+09:00 · `472439f68f78`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.anodyneQ_map_isIso_iff`<br>`SerrePositivity.SimplicialModel.UniverseLift.anodyneQ_map_isIso_reflect`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.PresentationKernelQuotient](#m0261)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.Simplicial.SmallDiagramQuotient](#m0571)<br>[HomotopicalAlgebra.Simplicial.SmallTargetKernelQuotient](#m0577)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.anodyneQ_map_isIso_iff` — 宇宙liftの前後でanodyne局所化の可逆性が同値となる。|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.anodyneQ_map_isIso_reflect` — 宇宙lift後のanodyne局所化可逆性から元の局所化可逆性を反映する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0590"></a>

### m0590 · HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftClosedComposition.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftClosedComposition.lean)|
|追加|2026-10-17T08:19:31+09:00 · `312d85972ec6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLiftClosedComposition.composition`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLiftClosedComposition.composition` — 実際の宇宙比較が内部Homの標準合成を保つ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0591"></a>

### m0591 · HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftClosedCurry.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftClosedCurry.lean)|
|追加|2026-10-17T08:19:31+09:00 · `312d85972ec6`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLiftClosedCurry.evaluation`|
|直接import元|[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLiftClosedCurry.evaluation` — 実際の宇宙比較が内部Homの評価と整合する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0592"></a>

### m0592 · HomotopicalAlgebra.Simplicial.UniverseLiftElements

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftElements.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftElements.lean)|
|追加|2026-10-16T23:14:10+09:00 · `4dd2d4172c1a`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.elementsEquivalence`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTotalEvaluation](#m0232)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.elementsEquivalence` — 既知の宇宙liftの単体圏と元の単体圏の同値を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0593"></a>

### m0593 · HomotopicalAlgebra.Simplicial.UniverseLiftFillers

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftFillers.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftFillers.lean)|
|追加|2026-10-16T11:58:45+09:00 · `bfdca7e488b2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.boundaryFillers`|
|直接import元|[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSections](#m0530)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftElements](#m0592)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftTensor](#m0603)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationChoices](#m0047)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare](#m0048)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixed](#m0050)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationMixedContext](#m0051)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPost](#m0053)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPre](#m0056)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.BiresolutionRightAction](#m0062)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices](#m0130)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence](#m0133)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws](#m0147)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionChoices](#m0149)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionParameterDiagram](#m0150)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindex](#m0151)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws](#m0152)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedCompatibility](#m0156)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint](#m0160)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation](#m0161)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomotopyDescent](#m0197)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNormalizedCompositionTriangle](#m0202)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero](#m0204)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReference](#m0205)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeComposition](#m0208)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle](#m0209)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent](#m0211)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex](#m0223)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceContraction](#m0224)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy](#m0225)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceHom](#m0227)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection](#m0229)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison](#m0234)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitCoherence](#m0235)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarUnitTriangles](#m0236)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowComparisonEndpoints](#m0278)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowDiagram](#m0282)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowParameters](#m0284)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarEvaluation](#m0290)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarReference](#m0293)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedIntervalRestrictions](#m0321)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)<br>[HomotopicalAlgebra.Simplicial.BoundaryFillerLifting](#m0353)<br>[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)<br>[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)<br>[HomotopicalAlgebra.Simplicial.LargeParameterHomotopy](#m0442)<br>[HomotopicalAlgebra.Simplicial.LargeParameterMapping](#m0443)<br>[HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice](#m0444)<br>[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)<br>[HomotopicalAlgebra.Simplicial.NerveBiparameterEvaluation](#m0461)<br>[HomotopicalAlgebra.Simplicial.NerveCylinderExtension](#m0469)<br>[HomotopicalAlgebra.Simplicial.NerveFillerExtension](#m0472)<br>[HomotopicalAlgebra.Simplicial.NerveFirstChoice](#m0473)<br>[HomotopicalAlgebra.Simplicial.NerveLargeParameter](#m0476)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveMovingFamilyFit](#m0481)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameter](#m0483)<br>[HomotopicalAlgebra.Simplicial.NerveMovingParameterRelative](#m0484)<br>[HomotopicalAlgebra.Simplicial.NerveRelativeNaturalBoundary](#m0492)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSectionHomotopy](#m0528)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSections](#m0530)<br>[HomotopicalAlgebra.Simplicial.SmallKanHomotopy](#m0573)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry](#m0591)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftElements](#m0592)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy](#m0594)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy](#m0595)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom](#m0600)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftTensor](#m0603)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.boundaryFillers` — 小さい値の境界充填を単体的宇宙liftへ移す。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0594"></a>

### m0594 · HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy

|項目|記録|
|---|---|
|分類|B|
|ソース|[UniverseLiftFixedHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftFixedHomotopy.lean)|
|追加|2026-10-16T16:24:53+09:00 · `6a4960a942c1`|
|主な公開宣言|`SerrePositivity.SimplicialModel.RelativeChoiceSpace.FixedBoundaryHomotopy.ofEdge`<br>`SerrePositivity.SimplicialModel.UniverseLift.fixedHomotopyMap_relative`<br>`SerrePositivity.SimplicialModel.UniverseLift.fixedHomotopyMap_recover`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Lifting the same selected whole edge with its endpoints and entire relative boundary。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0595"></a>

### m0595 · HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftHomotopy.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftHomotopy.lean)|
|追加|2026-10-16T19:10:22+09:00 · `1a0688723145`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.homotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.HomotopyClasses](#m0402)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.homotopy` — 指定された全区間ホモトピーをモデル構造なしで宇宙liftへ移す。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0596"></a>

### m0596 · HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftHomotopyClasses.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftHomotopyClasses.lean)|
|追加|2026-10-16T19:38:32+09:00 · `472439f68f78`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.homotopyClassEquiv`|
|直接import元|[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection](#m0589)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom](#m0598)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.homotopyClassEquiv` — 宇宙liftの前後の実際の区間ホモトピー類の全単射を構成する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0597"></a>

### m0597 · HomotopicalAlgebra.Simplicial.UniverseLiftIteration

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftIteration.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftIteration.lean)|
|追加|2026-10-16T19:00:46+09:00 · `8f58d0eb8b63`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.iterationIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.RelativeBarSpan](#m0531)<br>[HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction](#m0532)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.iterationIso` — 二重の単体的宇宙liftを一つのliftへ平坦化する自然同型を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0598"></a>

### m0598 · HomotopicalAlgebra.Simplicial.UniverseLiftLocalizedHom

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftLocalizedHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftLocalizedHom.lean)|
|追加|2026-10-17T01:46:07+09:00 · `0c60cd4bf188`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.localized_map_eq_iff_homotopy`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.Simplicial.SmallKanHomotopy](#m0573)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent](#m0146)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallAction](#m0219)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallReference](#m0222)<br>[HomotopicalAlgebra.Simplicial.SmallKanHomotopy](#m0573)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.localized_map_eq_iff_homotopy` — 小さいKan値のlift間の局所化射の等式を元の実ホモトピーで判定する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0599"></a>

### m0599 · HomotopicalAlgebra.Simplicial.UniverseLiftPadding

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftPadding.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftPadding.lean)|
|追加|2026-10-16T22:09:27+09:00 · `465bb6792c0f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.paddingIso`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences](#m0134)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy](#m0206)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRightEvaluation](#m0216)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionBarRowHomotopy](#m0295)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.paddingIso` — 単体的宇宙liftに付けた余分な宇宙の余裕を除く自然同型を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0600"></a>

### m0600 · HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftParameterHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftParameterHom.lean)|
|追加|2026-10-17T03:40:33+09:00 · `db5028c13bfe`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLiftParameterHom.closedIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry](#m0591)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalClosedAction](#m0155)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies](#m0190)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractSystem](#m0214)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry](#m0591)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLiftParameterHom.closedIso` — 小さいパラメータ写像空間の宇宙liftを大きい内部Homと同型で結ぶ。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0601"></a>

### m0601 · HomotopicalAlgebra.Simplicial.UniverseLiftPiZero

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftPiZero.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftPiZero.lean)|
|追加|2026-10-17T03:06:56+09:00 · `963469946d86`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLiftPiZero.equiv`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryKanBarQuotient](#m0249)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryQuotientPiZero](#m0251)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLiftPiZero.equiv` — 実際の連結成分と単体的宇宙liftとの交換を表す全単射を構成する。|
|今後の用途|今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。|

<a id="m0602"></a>

### m0602 · HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftProductParameter.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftProductParameter.lean)|
|追加|2026-10-16T17:42:17+09:00 · `c543585aa9ca`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLiftProductParameter.iso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLiftProductParameter.iso` — 動く小さいパラメータと標準単体の直積を小さい宇宙の対象で表す同型を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0603"></a>

### m0603 · HomotopicalAlgebra.Simplicial.UniverseLiftTensor

|項目|記録|
|---|---|
|分類|A|
|ソース|[UniverseLiftTensor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/UniverseLiftTensor.lean)|
|追加|2026-10-16T16:24:53+09:00 · `6a4960a942c1`|
|主な公開宣言|`SerrePositivity.SimplicialModel.UniverseLift.tensorMap`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy](#m0594)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy](#m0595)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom](#m0600)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChainFamily](#m0137)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceChainTransfer](#m0141)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits](#m0174)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeNativeComparison](#m0212)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRetractTransfer](#m0215)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeChainTransfer](#m0220)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowSelectedIntervals](#m0285)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentDiagonal](#m0314)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedCoherentTriangles](#m0315)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedEdgeRecovery](#m0318)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedFaceSystems](#m0320)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedSmallFamilies](#m0326)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedTriangles](#m0328)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.SelectedIntervalDiagram](#m0333)<br>[HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest](#m0339)<br>[HomotopicalAlgebra.Simplicial.NerveLargeSampling](#m0477)<br>[HomotopicalAlgebra.Simplicial.NerveSmallFamilies](#m0494)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedComposition](#m0590)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftClosedCurry](#m0591)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftFixedHomotopy](#m0594)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopy](#m0595)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftHomotopyClasses](#m0596)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom](#m0600)<br>[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|
|stage 4 L/E/S|いずれも利用なし|
|入口の主張|`SerrePositivity.SimplicialModel.UniverseLift.tensorMap` — 単体的宇宙liftの直積と元の直積のliftとの実際の比較射を構成する。|
|今後の用途|今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。|

<a id="m0604"></a>

### m0604 · HomotopicalAlgebra.Simplicial.VertexTuples

|項目|記録|
|---|---|
|分類|C|
|ソース|[VertexTuples.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/VertexTuples.lean)|
|追加|2026-10-16T09:10:54+09:00 · `eaa95550cd85`|
|主な公開宣言|`SerrePositivity.SimplicialModel.VertexTuples.obj`<br>`SerrePositivity.SimplicialModel.VertexTuples.verticesMap_pointsMap`<br>`SerrePositivity.SimplicialModel.VertexTuples.vertex_pointsMap`|
|直接import元|[CategoryTheory.NerveVertices](#m0017)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)<br>[HomotopicalAlgebra.Simplicial.VertexTuplesFunctor](#m0605)|
|宣言参照元|[CategoryTheory.NerveVertices](#m0017)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationComparison](#m0049)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationPostRelative](#m0055)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftBaseChange](#m0064)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftMixedFamilies](#m0068)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPostComposition](#m0069)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftPreComposition](#m0070)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftRelative](#m0071)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftTuples](#m0072)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.CoherentLiftUnitFamilies](#m0074)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowElementary](#m0283)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTupleCoherence](#m0286)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionMixedDiagonalData](#m0316)<br>[HomotopicalAlgebra.Simplicial.VertexTuplesFunctor](#m0605)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|順序付き頂点列は一般的だが、anchored chainの表示以外の利用契約が未確定。|
|現状の構成|Simplicial ordered tuples and their prescribed vertices。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0605"></a>

### m0605 · HomotopicalAlgebra.Simplicial.VertexTuplesFunctor

|項目|記録|
|---|---|
|分類|C|
|ソース|[VertexTuplesFunctor.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/VertexTuplesFunctor.lean)|
|追加|2026-10-16T15:32:44+09:00 · `fb287c15ee25`|
|主な公開宣言|`SerrePositivity.SimplicialModel.VertexTuples.tupleFunctor`<br>`SerrePositivity.SimplicialModel.VertexTuples.vertexFunctor`<br>`SerrePositivity.SimplicialModel.VertexTuples.inclusionNatTrans`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionArrowTuples](#m0287)|
|stage 4 L/E/S|いずれも利用なし|
|判断を保留する理由|頂点列の関手性は一般的だが、anchored chain用の表示との切り分けが未確定。|
|現状の構成|Ordered tuple spaces and strict vertex inclusions as actual functors。frameによる導来写像空間と整合図式の厳密化に対応する足場。|

<a id="m0606"></a>

### m0606 · HomotopicalAlgebra.Simplicial.WeightedWordHom

|項目|記録|
|---|---|
|分類|B|
|ソース|[WeightedWordHom.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WeightedWordHom.lean)|
|追加|2026-10-17T08:39:44+09:00 · `a2db2e165b49`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WeightedWordHom.hom`<br>`SerrePositivity.SimplicialModel.WeightedWordHom.comparisonIso`<br>`SerrePositivity.SimplicialModel.WeightedWordHom.localized_projection_isIso`|
|直接import元|[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|宣言参照元|[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|An explicit contraction of word-weighted paths onto their underlying paths。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0607"></a>

### m0607 · HomotopicalAlgebra.Simplicial.WordPresentationAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationAction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationAction.lean)|
|追加|2026-10-17T07:45:39+09:00 · `3ff83b21eecb`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationAction.action`<br>`SerrePositivity.SimplicialModel.WordPresentationAction.family_identity`<br>`SerrePositivity.SimplicialModel.WordPresentationAction.family_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual simplicial evaluation and parameterized action of the presented word category。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0608"></a>

### m0608 · HomotopicalAlgebra.Simplicial.WordPresentationAugmentation

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationAugmentation.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationAugmentation.lean)|
|追加|2026-10-17T07:58:03+09:00 · `242f0f56cea2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationAugmentation.augmentation`<br>`SerrePositivity.SimplicialModel.WordPresentationAugmentation.diagonalConstIso`<br>`SerrePositivity.SimplicialModel.WordPresentationAugmentation.diagonalAugmentation`|
|直接import元|[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Natural augmentation of the simplicial word construction and its two-direction diagrams。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0609"></a>

### m0609 · HomotopicalAlgebra.Simplicial.WordPresentationCat

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationCat.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationCat.lean)|
|追加|2026-10-17T07:58:03+09:00 · `242f0f56cea2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationCat.functor`<br>`SerrePositivity.SimplicialModel.WordPresentationCat.simplicialFunctor`<br>`SerrePositivity.SimplicialModel.WordPresentationCat.bisimplicial`|
|直接import元|[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The presented word category as a functor of categories and simplicial word parameters。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0610"></a>

### m0610 · HomotopicalAlgebra.Simplicial.WordPresentationDiagram

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationDiagram.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationDiagram.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationDiagram.degreeMap_id`<br>`SerrePositivity.SimplicialModel.WordPresentationDiagram.identity_left`<br>`SerrePositivity.SimplicialModel.WordPresentationDiagram.identity_right`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSourceMap](#m0614)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordPresentationCat](#m0609)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSourceMap](#m0614)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The actual simplicial diagram of presented word categories。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0611"></a>

### m0611 · HomotopicalAlgebra.Simplicial.WordPresentationNaturality

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationNaturality.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationNaturality.lean)|
|追加|2026-10-17T07:45:39+09:00 · `3ff83b21eecb`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationNaturality.R`<br>`SerrePositivity.SimplicialModel.WordPresentationNaturality.natTrans`<br>`SerrePositivity.SimplicialModel.WordPresentationNaturality.small_naturality`|
|直接import元|[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Evaluation of every presented word arrow commutes with every simplex map。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0612"></a>

### m0612 · HomotopicalAlgebra.Simplicial.WordPresentationRealization

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationRealization.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationRealization.lean)|
|追加|2026-10-17T07:40:37+09:00 · `ca5e648b6977`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationRealization.parameterEvaluation`<br>`SerrePositivity.SimplicialModel.WordPresentationRealization.functor`<br>`SerrePositivity.SimplicialModel.WordPresentationRealization.smallFunctor`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual degreewise evaluation of the word presentation from strong contractions。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0613"></a>

### m0613 · HomotopicalAlgebra.Simplicial.WordPresentationSection

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationSection.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationSection.lean)|
|追加|2026-10-17T07:58:03+09:00 · `242f0f56cea2`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationSection.simplicialSection`<br>`SerrePositivity.SimplicialModel.WordPresentationSection.diagonalSection_app`<br>`SerrePositivity.SimplicialModel.WordPresentationSection.diagonalSection_augmentation`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The ambient source section of the actual diagonal word augmentation。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0614"></a>

### m0614 · HomotopicalAlgebra.Simplicial.WordPresentationSourceMap

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordPresentationSourceMap.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordPresentationSourceMap.lean)|
|追加|2026-10-17T07:51:16+09:00 · `a181718efc6f`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordPresentationSourceMap.commute`<br>`SerrePositivity.SimplicialModel.WordPresentationSourceMap.mapHomSame_unit`<br>`SerrePositivity.SimplicialModel.WordPresentationSourceMap.mapHomSame_comp`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.Simplicial.WordPresentationCat](#m0609)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordActionOperators](#m0238)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Actual maps of word Hom simplicial sets induced by arbitrary source functors。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0615"></a>

### m0615 · HomotopicalAlgebra.Simplicial.WordRetractChainFamily

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordRetractChainFamily.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordRetractChainFamily.lean)|
|追加|2026-10-17T07:29:06+09:00 · `01b49826a79d`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordRetractChainFamily.Chain`<br>`SerrePositivity.SimplicialModel.WordRetractChainFamily.evaluate_ofInterval`<br>`SerrePositivity.SimplicialModel.WordRetractChainFamily.transfer_ofInterval`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Finite retract chains with word parameters and arbitrary internal unit elimination。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0616"></a>

### m0616 · HomotopicalAlgebra.Simplicial.WordRetractionAction

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordRetractionAction.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordRetractionAction.lean)|
|追加|2026-10-17T07:25:19+09:00 · `2efc3cce9602`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordRetractionAction.split`<br>`SerrePositivity.SimplicialModel.WordRetractionAction.action_over`<br>`SerrePositivity.SimplicialModel.WordRetractionAction.action_section`|
|直接import元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|Extend an actual strong contraction to a strict action of interval words。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0617"></a>

### m0617 · HomotopicalAlgebra.Simplicial.WordSegment

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordSegment.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordSegment.lean)|
|追加|2026-10-17T07:17:56+09:00 · `1f744bb07092`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordSegment.interval`<br>`SerrePositivity.SimplicialModel.WordSegment.vertex_one_letter`<br>`SerrePositivity.SimplicialModel.WordSegment.contraction`|
|直接import元|[HomotopicalAlgebra.Simplicial.WordPresentationDiagram](#m0610)<br>[HomotopicalAlgebra.Simplicial.WordRetractionAction](#m0616)<br>[HomotopicalAlgebra.Simplicial.WordSegmentComparison](#m0618)|
|宣言参照元|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison](#m0132)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAction](#m0153)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalAmbientHom](#m0154)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation](#m0157)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarDiagonalHomRetraction](#m0159)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation](#m0165)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedRowWordHom](#m0167)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation](#m0169)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution](#m0170)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeWordChainTransfer](#m0195)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSmallFreeWordChainTransfer](#m0221)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding](#m0230)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordAction](#m0237)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordChainFamily](#m0239)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordContraction](#m0240)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators](#m0242)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordPresentation](#m0243)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordResolution](#m0244)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowMaps](#m0245)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRows](#m0246)<br>[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal](#m0247)<br>[HomotopicalAlgebra.Simplicial.FreeWordHom](#m0400)<br>[HomotopicalAlgebra.Simplicial.WeightedWordHom](#m0606)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAction](#m0607)<br>[HomotopicalAlgebra.Simplicial.WordPresentationAugmentation](#m0608)<br>[HomotopicalAlgebra.Simplicial.WordPresentationCat](#m0609)<br>[HomotopicalAlgebra.Simplicial.WordPresentationDiagram](#m0610)<br>[HomotopicalAlgebra.Simplicial.WordPresentationNaturality](#m0611)<br>[HomotopicalAlgebra.Simplicial.WordPresentationRealization](#m0612)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSection](#m0613)<br>[HomotopicalAlgebra.Simplicial.WordPresentationSourceMap](#m0614)<br>[HomotopicalAlgebra.Simplicial.WordRetractChainFamily](#m0615)<br>[HomotopicalAlgebra.Simplicial.WordRetractionAction](#m0616)<br>[HomotopicalAlgebra.Simplicial.WordSegmentComparison](#m0618)|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|A simplicial monoid segment built from finite interval words。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

<a id="m0618"></a>

### m0618 · HomotopicalAlgebra.Simplicial.WordSegmentComparison

|項目|記録|
|---|---|
|分類|B|
|ソース|[WordSegmentComparison.lean](../SerrePositivity/HomotopicalAlgebra/Simplicial/WordSegmentComparison.lean)|
|追加|2026-10-17T07:17:56+09:00 · `1f744bb07092`|
|主な公開宣言|`SerrePositivity.SimplicialModel.WordSegmentComparison.point`<br>`SerrePositivity.SimplicialModel.WordSegmentComparison.localized_projection_isIso`<br>`SerrePositivity.SimplicialModel.WordSegmentComparison.localized_letter_isIso`|
|直接import元|[HomotopicalAlgebra.Foundations](../SerrePositivity/HomotopicalAlgebra/Foundations.lean)|
|宣言参照元|なし|
|stage 4 L/E/S|いずれも利用なし|
|構成と数学的対応|The finite-word segment and the interval agree in anodyne localization。自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。|

## Foundationsの閉包と配置の整理案（未実施）

プロジェクト内ソースだけのFoundations閉包は1030本。そのうちBは411本（39.9%）、今回追加集合は616本。B全413本の残り2本は停止時に保存した `NormalizedHornTargetFaces` と `NormalizedHornTargetAssociativity` で、Foundationsには未収録である。Mathlib・Lean本体のモジュール数を分母に混ぜていない。

Aのうち21本がBを直接importする。Aを現在のまま全部残してBだけ閉包から除くことはできない。次が境界整理の対象。

|Aのモジュール|直接依存するB|
|---|---|
|[CategoryTheory.ArrowFactorizationCategory](#m0007)|[CategoryTheory.AnchoredChain](#m0001)|
|[CategoryTheory.NerveSimplexFirstFunctor](#m0015)|[CategoryTheory.LabelledChain](#m0010)|
|[CategoryTheory.Quiver.PathObjectTransport](#m0036)|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution](#m0098)|
|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathDegeneracyImage](#m0097)|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo](#m0099)|
|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionPresentation](#m0100)|[HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution](#m0098)|
|[HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints](#m0341)|[HomotopicalAlgebra.Simplicial.RelativeChoiceSpace](#m0541)|
|[HomotopicalAlgebra.Simplicial.BoundaryCotensor](#m0352)|[HomotopicalAlgebra.Simplicial.RelativeChoiceSpace](#m0541)|
|[HomotopicalAlgebra.Simplicial.BoundaryOneCotensor](#m0355)|[HomotopicalAlgebra.Simplicial.RelativeChoiceSpace](#m0541)|
|[HomotopicalAlgebra.Simplicial.ClosedParameterUnits](#m0362)|[HomotopicalAlgebra.Simplicial.BinaryIntervalTriangles](#m0350)|
|[HomotopicalAlgebra.Simplicial.CurriedHomotopy](#m0376)|[HomotopicalAlgebra.Simplicial.LargeParameterSquare](#m0445)|
|[HomotopicalAlgebra.Simplicial.KanHomotopyExtension](#m0414)|[HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison](#m0404)|
|[HomotopicalAlgebra.Simplicial.LargeParameterExtension](#m0441)|[HomotopicalAlgebra.Simplicial.RelativeChoiceSpace](#m0541)|
|[HomotopicalAlgebra.Simplicial.ParameterCube](#m0510)|[HomotopicalAlgebra.Simplicial.RetractChainFamily](#m0547)|
|[HomotopicalAlgebra.Simplicial.ReversedSimplexParameters](#m0550)|[HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionDegeneracyValues](#m0182)|
|[HomotopicalAlgebra.Simplicial.SimplexInverseMatching](#m0558)|[HomotopicalAlgebra.Simplicial.NerveCoherentFamily](#m0466)|
|[HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation](#m0563)|[CategoryTheory.SimplexChainParameter](#m0045)|
|[HomotopicalAlgebra.Simplicial.SimplexNerveFunctor](#m0565)|[CategoryTheory.LabelledChain](#m0010)|
|[HomotopicalAlgebra.Simplicial.SimplexNerveStandard](#m0567)|[HomotopicalAlgebra.Simplicial.NerveInitialImage](#m0474)|
|[HomotopicalAlgebra.Simplicial.SmallDominatedSubcomplex](#m0572)|[HomotopicalAlgebra.Simplicial.SmallParameterClosure](#m0574)|
|[HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation](#m0583)|[CategoryTheory.LabelledChain](#m0010)<br>[CategoryTheory.SimplexChainParameter](#m0045)|
|[HomotopicalAlgebra.Simplicial.UniverseLiftProductParameter](#m0602)|[HomotopicalAlgebra.Simplicial.NerveProductParameter](#m0490)|

試算：Foundationsの直接importのうち、推移閉包にBを含む入口をすべて除く保守的な仮想入口は199本の直接import、閉包453本になる。ただしAも153本が入口から失われるため、そのまま採用する案ではない。測定用の仮想入口は/tmpに置き、共有Foundationsは変更していない。

### ビルド時間の測定

測定日は2026-10-17。同一の固定版Lean/Mathlibと作業環境で実行した。並行作業のある環境の観測値であり、速度保証やcold buildの推計にはしない。

|測定|実測|意味|
|---|---|---|
|編集前のキャッシュ済みFoundations build|4.30秒|3274 jobs、再コンパイル不要の基準値|
|編集後のキャッシュ済みFoundations build|4.50秒（3回中央値）|4.79 / 4.50 / 4.35秒。コメント変更後の通常の無変更build|
|Foundations全体のimport型検査|10.68秒（3回中央値）|10.77 / 10.68 / 9.03秒。/tmpの1行import、プロジェクト閉包1030本|
|Bを含む入口を除いた仮想import型検査|8.42秒（3回中央値）|8.11 / 8.78 / 8.42秒。/tmpの199 import、閉包453本、Bゼロ、A153本も脱落|
|Simplicialの文書変更を中心とする対象build|193.71秒（wall）|3276 jobs。Lean/Lakeの依存キャッシュを保持した増分再コンパイル|
|書式修正後の全618本＋Foundations対象build|49.66秒（wall）|3276 jobs、警告・エラーなし。再コンパイル39本、残りは検証済みキャッシュ|

全体と仮想入口の読み込み中央値の差は2.26秒。ただしBだけの有無を比較した実験ではなく、Aを含む依存も減っている。一般道具を保持した将来の分離後の節約時間としては引用しない。

Simplicial側の測定ログで今回追加集合の再コンパイル時間を記録できた283本はA151・B121・C11本。各ジョブの経過時間の合計は1496.9秒、そのうちB121本は720.2秒（48.1%）。これは並列ジョブの合計であってwall timeではない。Bのコメント変更でもコンパイルが必要になる実際の負担は確認できるが、B全413本のcold buildコストや、Bを外した場合のwall time削減量をこの値から算出しない。

キャッシュの削除・clean・強制的な全Mathlib再構築は行っていない。承認後の配置作業では、Aの利用可能性を等しくした二つの入口を用意し、同じキャッシュ条件・並列度で増分buildとimport型検査を改めて比較する。

### 配置案と実施順（承認後）

たとえば `ArrowFactorizationCategory` は一般的な因子分解圏を与えるが、入力構造 `ArrowFactorization` がBの `AnchoredChain` に同居している。この種の定義の同居を先に解く必要があり、ディレクトリ名の変更だけでは依存は減らない。


1. まず上の21本のA→Bの辺を点検し、一般的な定義・補題を独立した下層へ切り出す設計を作る。C15本は利用契約・仮定を確定してから分類する。今回はこの切り出しも行わない。
2. Bのための `HomotopicalAlgebra/Rectification/` と任意importの入口を設計する。CategoryTheoryのBをそこへまとめるか、CategoryTheoryの下に専用表示層を残すかは、圏論の独立性と名前空間の安定性を比較して決める。ファイルパスとLean名前空間を同一視せず、公開名は可能な限り保つ。
3. 互換importファイルを旧パスに残す段階を設け、B同士・Aとの境界・個別チェック・文書リンクのimportを更新する。旧パスのwrapperをFoundationsがimportし続けると閉包は減らないため、共有入口では一般層だけへ切り替える必要がある。
4. Foundationsの削減は、stage 4のL/E/S入口と指定分解版F1/F2の契約を再監査してから行う。ルート `SerrePositivity.lean`、Foundations、共有監査の変更は自分のhunkだけ `git add -p` でstageする。今回それらは未変更。
5. `scripts/audit_homotopical_foundations.lean` のimport閉包・宣言数と、`scripts/audit_stage4_dependencies.py` のbaseline/入口、`scripts/audit_stage4_contract.lean` の監査対象を再確認する。パスを列挙する検索・project map・個別監査も新パスへ更新する。単なる宣言数の減少を公理依存の改善と取り違えない。
6. 上の逆依存表を使い、別チャットが作業中の個別import・未コミットファイル・未追跡チェックへの影響を先に確認する。旧パス互換を残して段階的に切り替え、並行作業の途中で削除しない。連絡や他チャットのコード変更は別途合意する。
7. 旧パス互換ありの対象ビルド、Foundations、L/E/Sの依存・公理監査を通し、一般入口と任意のRectification入口を別々に測定する。受入条件は公開宣言の契約維持、stage 4閉包へのB混入なし、一般入口のBゼロ、必要な一般道具の利用可能性、標準公理以外の新規依存なし。条件を満たした後に互換ファイルを残す期間を決める。

移動・削除・import削減・証明の再設計は承認待ちであり、今回の変更には含めない。

## docstring整備・検証

618本のモジュールdocstringを「概要／方針（定義・証明）／規約と注意／使われ方」の10〜30行に統一した。A190本では主要205公開宣言を日本語で整備し、仮定・証明方針・用途を記した。B/Cは中断中の構成・本棚卸しの固定アンカー・k-theory.md §396を明示した。元の技術的注記は通常コメントとして保存した。

- CategoryTheory・Reedyほか56本：対象build 1525 jobsで成功。コミット `cdade5b7`。
- HomotopyFunctionComplex直下282本：対象build 2979 jobsで成功。コミット `f3da3d4d`。
- Simplicial 280本＋Foundations：対象build 3276 jobsで成功。コミット `3bec0093`。
- 宣言docstringの空行・技術注記の改行とnerveの表現を補正し、新コミット `b49c9d9d` へ保存。amend・rebase・resetは使用していない。
- 最終状態で全618本とFoundationsの対象buildが3276 jobsで成功。最終ログにwarning/errorなし。
- 618本すべてで、文字列を保持し入れ子コメント・行コメントと空白を除いたテキストが編集前と完全一致。宣言名・型・証明・importに変更なし。対象の `git diff --check` も成功。
- stage 4依存監査：79入口・663本、§224以降の対象依存0、baselineから変化した到達モジュール0。
- stage 4契約監査：8392宣言・660宣言元モジュール、標準3公理のみ。
- Foundations公理監査：14216宣言・1004宣言元モジュール、標準3公理のみ。
- Foundations未収録の停止時保存2本も別途監査：23宣言、標準3公理のみ。

新しいsorry・axiom・Leanの外部引用宣言は追加していない。上記の文献リンクは技法を探すための対応情報である。ルート・Foundations・共有監査スクリプトを編集せず、他チャットの差分・未追跡ファイルは保存した。
