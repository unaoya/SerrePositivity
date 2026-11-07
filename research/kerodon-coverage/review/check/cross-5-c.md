# 第5章の交差抜き取り検査（research/kerodon-review-c）

- 対象は main の `dc3ebc8ab`。依頼に従い第4〜6章を選んだ。既存の同名の抜き取り報告と区別するため、ファイル名に `-c` を付けた。
- 乱数の種は `0x81e593fc`。Python 3.14.7 の `random.Random(seed).sample` で、章を 4→5→6、区分を own・both・mathlib の合算→none の順に処理した。各母集団は項目番号の数値順、各区分は重複なしの20件。
- 元表の status と引用で抽出・型の取得を行い、Kerodon 本文、段1・段1′と章別 kernel evidence の型、Lean ソースから判定した。元表の reason は判定に使っていない。
- none では (a) 元の citations.csv と Lean docstring の該当番号・同小節の引用、(b) 宣言名と型の語索引を原方向・双対・普通圏の語で検索、(c) 同小節の own・both の引用ファイルと同じディレクトリの宣言を検索した。近傍は起点がなければ mathlib・partial、同小節の引用、候補の順で補った。候補の採否は各行の型・ソースとの照合による。
- 差は status の変更で数えた。§8.1 に従い、特例・一方向・強い仮定・複数結論の一部が直接確認できる場合を partial とした。

| 元の区分 | 母集団 | 抽出 | 差 | 差の割合 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 48 | 20 | 0 | 0% |
| none | 118 | 20 | 2 | 10% |

## own・both・mathlib

| Kerodon | 元の status | 照合結果 | 仮定・結論と確認した宣言 |
|---|---|---|---|
| [5.1.1.10](https://kerodon.net/tag/01TC) | own | own | 仮定：両端は準圏、q は inner fibration（一致）。結論：恒等辺の cocartesian 性は constant 版、cartesian 性は恒等辺が可逆であることと isCartesianEdge_of_isInvertibleEdge で得る（一致）。 `SerrePositivity.InfinityCategories.isCocartesianEdge_constant` (SerrePositivity/InfinityCategories/F1/Fibrations/InvertibleCartesian.lean:53), `SerrePositivity.InfinityCategories.isCartesianEdge_of_isInvertibleEdge` (SerrePositivity/InfinityCategories/F1/Fibrations/InvertibleCartesian.lean:25) |
| [5.1.4.1](https://kerodon.net/tag/01UA) | own | own | 仮定：任意の単体集合の射（一致）。結論：CartesianFibration と CocartesianFibration の inner fibration と終点／始点を指定した辺 lift の定義が一致する（一致）。 `SerrePositivity.InfinityCategories.CartesianFibration` (SerrePositivity/InfinityCategories/F1/Fibrations/CartesianFibration.lean:46), `SerrePositivity.InfinityCategories.cartesianFibrations` (SerrePositivity/InfinityCategories/F1/Fibrations/CartesianFibration.lean:24), `SerrePositivity.InfinityCategories.CocartesianFibration` (SerrePositivity/InfinityCategories/F1/Fibrations/CartesianFibration.lean:53), `SerrePositivity.InfinityCategories.CocartesianHornFibration` (SerrePositivity/InfinityCategories/Core/CocartesianFibration.lean:23) |
| [5.2.3.11](https://kerodon.net/tag/024C) | own | own | 仮定：C,D,E は準圏で E への射を指定（一致）。結論：その relativeJoin 自体が準圏（一致）。 `SerrePositivity.InfinityCategories.relativeJoin_quasicategory` (SerrePositivity/InfinityCategories/F1/Joins/JoinQuasicategory.lean:58), `SerrePositivity.InfinityCategories.relativeJoinProjection_innerFibration` (SerrePositivity/InfinityCategories/F1/Joins/JoinQuasicategory.lean:67) |
| [5.2.4.5](https://kerodon.net/tag/024R) | own | own | 仮定：任意の f:X→Y（一致）。結論：Δ¹×X と Y の厳密な pushout から相対 join への指定の比較が IsPrecompositionEquivalence なので categorical pushout（一致）。 `SerrePositivity.InfinityCategories.isPrecompositionEquivalence_relativeJoinCylinderComparison` (SerrePositivity/InfinityCategories/F1/Joins/RelativeJoinCylinderEquivalence.lean:48), `SerrePositivity.InfinityCategories.relativeJoinCylinderComparison` (SerrePositivity/InfinityCategories/F1/Joins/RelativeJoinCylinder.lean:72) |
| [5.2.6.2](https://kerodon.net/tag/01Q9) | mathlib | mathlib | 仮定：集合値前層 F（一致）。結論：Functor.Elements F の反対圏を取り、対象 (C,x)、射 f と F(f)(x')=x、第一成分射影を得る。costructuredArrowYonedaEquivalence の始域がこの圏（一致）。 `CategoryTheory.Functor.Elements.costructuredArrowYonedaEquivalence` (Mathlib/CategoryTheory/Elements.lean:208) |
| [5.3.1.10](https://kerodon.net/tag/02T1) | own | own | 仮定：同じ基底上の二つの cocartesian fibration（一致。構成は任意の基底射にも定義）。結論：relativeFunctorSpace の頂点を cocartesian 辺保存で切った充満部分単体集合。相対 functor space の準圏性をこの仮定で適用する（一致）。 `SerrePositivity.InfinityCategories.cocartesianRelativeFunctorSpace` (SerrePositivity/InfinityCategories/F1/Cocartesian/RelativeFunctor.lean:40), `SerrePositivity.InfinityCategories.cocartesianRelativeFunctorPredicate` (SerrePositivity/InfinityCategories/F1/Cocartesian/RelativeFunctor.lean:26) |
| [5.3.2.3](https://kerodon.net/tag/035X) | own | own | 仮定：普通圏間の H と SSet 値 F（一致）。結論：simplicialReplacementBaseMap_isPullback が指定正方形、simplicialReplacementFiberMap_isIso が F(c) と指定ファイバーの同型（一致）。 `SerrePositivity.InfinityCategories.simplicialReplacementBaseMap` (SerrePositivity/InfinityCategories/F1/Diagrams/SimplicialReplacementBaseChange.lean:26), `SerrePositivity.InfinityCategories.simplicialReplacementBaseMap_isPullback` (SerrePositivity/InfinityCategories/F1/Diagrams/SimplicialReplacementBaseChange.lean:45) |
| [5.3.2.11](https://kerodon.net/tag/0365) | own | own | 仮定：[n] 形の図式（定義は普通圏全般で弱い）。結論：simplicialReplacement を [n] に特殊化すると本文の mapping simplex（一致）。 `SerrePositivity.InfinityCategories.simplicialReplacement` (SerrePositivity/InfinityCategories/F1/Diagrams/SimplicialReplacement.lean:41) |
| [5.3.2.13](https://kerodon.net/tag/0366) | own | own | 仮定：[1] 形の任意の射（一致）。結論：simplicialReplacementIntervalIso が {1} 側を貼る prism pushout との同型を与える（一致）。 `SerrePositivity.InfinityCategories.simplicialReplacementIntervalIso` (SerrePositivity/InfinityCategories/F1/Scaffold/ScaffoldIntervalPushout.lean:57), `SerrePositivity.InfinityCategories.scaffoldInterval_isPushout` (SerrePositivity/InfinityCategories/F1/Scaffold/ScaffoldIntervalPushout.lean:23) |
| [5.3.4.11](https://kerodon.net/tag/0373) | own | own | 仮定：普通圏上の SSet 値図式（一致）。結論：tautScaffoldDiagram が各 prefix への制限と F の写像の合成で重み付き単体を作り、tautScaffold がこれを単体写像にする（一致）。 `SerrePositivity.InfinityCategories.tautScaffold` (SerrePositivity/InfinityCategories/F1/Scaffold/TautScaffold.lean:44), `SerrePositivity.InfinityCategories.tautScaffoldDiagram` (SerrePositivity/InfinityCategories/F1/Scaffold/TautScaffold.lean:23) |
| [5.3.4.12](https://kerodon.net/tag/0374) | own | own | 仮定：普通圏上の SSet 値図式（一致）。結論：tautScaffold の後に weightedNerveProjection を合成した射は simplicialReplacementProjection と等しい（一致）。 `SerrePositivity.InfinityCategories.tautScaffold_projection` (SerrePositivity/InfinityCategories/F1/Scaffold/TautScaffold.lean:72) |
| [5.3.4.14](https://kerodon.net/tag/0376) | own | own | 仮定：任意の普通圏関手で基底を変更（一致）。結論：両者の基底変更同型のもとで tautScaffold の正方形が可換で、再構成した比較が基底変更比較になる（一致）。 `SerrePositivity.InfinityCategories.tautScaffold_map` (SerrePositivity/InfinityCategories/F1/Diagrams/SimplicialReplacementFunctor.lean:92), `SerrePositivity.InfinityCategories.tautScaffold_baseMap_isPullback` (SerrePositivity/InfinityCategories/F1/Diagrams/SimplicialReplacementBaseChange.lean:77) |
| [5.3.4.17](https://kerodon.net/tag/0379) | own | own | 仮定：各 F(c) が準圏（一致）。結論：指定された tautScaffold に CocartesianScaffold を与える（一致）。 `SerrePositivity.InfinityCategories.tautScaffold_isCocartesianScaffold` (SerrePositivity/InfinityCategories/F1/Weighted/NerveCocartesianScaffold.lean:33), `SerrePositivity.InfinityCategories.tautScaffold_isLeftScaffold` (SerrePositivity/InfinityCategories/F1/Scaffold/LeftScaffold.lean:35) |
| [5.3.4.19](https://kerodon.net/tag/037B) | own | own | 仮定：各 F(c) が準圏（一致）。結論：指定 weightedNerve の strict transport への自然変換と各成分の IsQCatEquivalence（一致）。 `SerrePositivity.InfinityCategories.weightedNerveCocartesianTransportUnit` (SerrePositivity/InfinityCategories/F1/Weighted/NerveCocartesianUnit.lean:71), `SerrePositivity.InfinityCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence` (SerrePositivity/InfinityCategories/F1/Weighted/NerveCocartesianUnit.lean:113) |
| [5.3.5.12](https://kerodon.net/tag/037V) | own | own | 仮定：普通圏 C の nerve 上の二つの cocartesian fibration（一致）。結論：相対 cocartesian functor space から二つの strict transport 図式間の enriched mapping space への指定写像が IsQCatEquivalence（一致）。 `SerrePositivity.InfinityCategories.cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence` (SerrePositivity/InfinityCategories/F1/Cocartesian/StrictTransportMappingEquivalence.lean:48), `SerrePositivity.InfinityCategories.cocartesianStrictTransportInfinityMap_isFullyFaithful` (SerrePositivity/InfinityCategories/F1/Cocartesian/StrictTransportEnriched.lean:52) |
| [5.5.2.1](https://kerodon.net/tag/01ZW) | own | own | 仮定：一点 Kan 複体を持つ SpaceInfinity（一致）。結論：PointedSpaceInfinity の本体は pointSpaceVertex の sliceUnder（一致）。 `SerrePositivity.InfinityCategories.PointedSpaceInfinity` (SerrePositivity/InfinityCategories/F1/Categories/PointedSpaces.lean:60), `SerrePositivity.InfinityCategories.pointedSpaceFiberVertexEquiv` (SerrePositivity/InfinityCategories/F1/StraighteningLeft/PointedSpaceFiberVertices.lean:25), `SerrePositivity.InfinityCategories.SpaceInfinity` (SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean:103) |
| [5.5.3.3](https://kerodon.net/tag/020B) | own | own | 仮定：小さい準圏を対象とし enriched Hom に core を取る QC（一致）。結論：catInfinity_quasicategory がその coherent nerve の準圏性を与える（一致）。 `SerrePositivity.InfinityCategories.catInfinity_quasicategory` (SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean:30), `SerrePositivity.InfinityCategories.quasicategoryCore_kanComplex` (SerrePositivity/InfinityCategories/F1/Categories/CoreKan.lean:61), `SerrePositivity.InfinityCategories.qCat_sHom_kanComplex` (SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:99) |
| [5.5.4.1](https://kerodon.net/tag/020K) | own | own | 仮定：小さい準圏（一致）。結論：QuasicategoryObject の enriched Hom は制限前の internal Hom X⟹Y で、SimplicialNerve を適用して指定 coherent nerve を得る（一致）。 `SerrePositivity.InfinityCategories.QuasicategoryObject` (SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:24), `SerrePositivity.InfinityCategories.quasicategoryObject_enrichedCategory` (SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:48), `SerrePositivity.InfinityCategories.quasicategoryObject_simplicialCategory` (SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:60), `CategoryTheory.SimplicialNerve` (Mathlib/AlgebraicTopology/SimplicialNerve.lean:190) |
| [5.6.1.1](https://kerodon.net/tag/025N) | mathlib | mathlib | 仮定：LocallyDiscrete C から Cat への Pseudofunctor（一致）。結論：Pseudofunctor.Grothendieck とその Category instance は対 (C,X)、射 (f,F(f)X→Y) と mapComp の逆による合成を持つ（一致）。 `CategoryTheory.Pseudofunctor.Grothendieck` (Mathlib/CategoryTheory/Bicategory/Grothendieck.lean:77), `CategoryTheory.Pseudofunctor.Grothendieck.category` (Mathlib/CategoryTheory/Bicategory/Grothendieck.lean:139), `CategoryTheory.Grothendieck` (Mathlib/CategoryTheory/Grothendieck.lean:73) |
| [5.6.1.5](https://kerodon.net/tag/025P) | mathlib | mathlib | 仮定：LocallyDiscrete Cᵒᵖ から Cat への Pseudofunctor（一致）。結論：Pseudofunctor.CoGrothendieck とその Category instance は対 (C,X)、射 (f,X→F(f)Y) と mapComp による合成を持つ（一致）。 `CategoryTheory.Pseudofunctor.CoGrothendieck` (Mathlib/CategoryTheory/Bicategory/Grothendieck.lean:238), `CategoryTheory.Pseudofunctor.CoGrothendieck.category` (Mathlib/CategoryTheory/Bicategory/Grothendieck.lean:298) |

## none

### [5.1.4.19](https://kerodon.net/tag/01UQ) · `none → none`

前者は辺から一点への制限射自体の trivial Kan 性、後者は固定準圏への余錐の apex の可逆性。任意の inner fibration q と A⊆B に対する q' 上の辺保存は得られない。

- (a) `5.1.4.19` と `5.1.4`、`Kerodon`。直接 0 件、同小節 75 件。参照例 `SerrePositivity/InfinityCategories/Core/CocartesianCoslice.lean:7`, `SerrePositivity/InfinityCategories/Core/CocartesianCosliceFiber.lean:6`。
- (b) `cartesian coslice restriction / relative coslice pullback edge / cocartesian slice restriction`。双対の語 `cartesian cocartesian coslice edge pushout relative restriction slice`。普通圏の語 `cocartesian coslice edge pullback relative restriction slice`。確認した候補 `relativeCosliceRestriction_source_of_isCocartesianEdge` (`SerrePositivity/InfinityCategories/F1/Cocartesian/SourceRestriction.lean:42`), `isCartesianEdge_coconeRestriction_of_apex` (`SerrePositivity/InfinityCategories/F1/CoconeRestrictionCartesianEdge.lean:39`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 2634 件。

### [5.1.5.10](https://kerodon.net/tag/01V6) · `none → none`

大域的 cocartesian 辺の三角での合成と大域 fibration の輸送。局所 lift の三角閉性から大域性を導く判定を確認できない。

- (a) `5.1.5.10` と `5.1.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `locally cartesian fibration / locally cocartesian triangle composition / fiber transport comp`。双対の語 `cartesian cocartesian comp composition fiber fibration locally transport triangle`。普通圏の語 `cocartesian comp composition fiber fibre lifting locally pullback transport triangle`。確認した候補 `isCocartesianEdge_triangle_longEdge` (`SerrePositivity/InfinityCategories/F1/Cocartesian/Composition.lean:23`), `homotopyTransport_map_isTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:68`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory/FiberedCategory`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 480 件。

### [5.3.4.22](https://kerodon.net/tag/037E) · `none → none`

両者は係数に準圏性を要求し、scaffold 性または前合成同値を与える。全ての F(f) が同型という別の仮定で λ_t 自体が厳密同型になる型は確認できない。

- (a) `5.3.4.22` と `5.3.4`、`Kerodon`。直接 0 件、同小節 101 件。参照例 `SerrePositivity/InfinityCategories/F1/Diagrams/StrictDiagramScaffoldAdjunction.lean:8`, `SerrePositivity/InfinityCategories/F1/Weighted/NerveTransportUnit.lean:37`。
- (b) `taut scaffold isIso / weighted nerve simplicial replacement pointwise iso / locally constant weighted nerve`。双対の語 `constant iso locally nerve pointwise replacement scaffold simplicial taut weighted`。普通圏の語 `coherent constant iso locally nerve pointwise replacement scaffold simplicial taut weighted`。確認した候補 `tautScaffold_isCocartesianScaffold` (`SerrePositivity/InfinityCategories/F1/Weighted/NerveCocartesianScaffold.lean:33`), `tautScaffold_isPrecompositionEquivalence_of_quasicategory` (`SerrePositivity/InfinityCategories/F1/Weighted/NerveCocartesianScaffold.lean:43`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Diagrams`, `SerrePositivity/InfinityCategories/F1/Scaffold`, `SerrePositivity/InfinityCategories/F1/Weighted`, `SerrePositivity/InfinityCategories/F1B/CocartesianScaffold` を検索。対象の宣言見出し 1234 件。

### [5.3.6.11](https://kerodon.net/tag/0474) · `none → none`

輸送の構成は cocartesian 側、相対関手空間は辺保存で切る。Fun(E/B,D) の cartesian 輸送を Fun(-,D) との合成に同定する型がない。

- (a) `5.3.6.11` と `5.3.6`、`Kerodon`。直接 0 件、同小節 44 件。参照例 `SerrePositivity/InfinityCategories/F1B/Fibrations/FiberwiseHomFinalVertex.lean:8`, `SerrePositivity/InfinityCategories/F1B/Fibrations/FiberwiseHomInnerFibration.lean:5`。
- (b) `relative functor cartesian homotopy transport / contravariant functor transport postcomposition / fiberwise internal hom`。双対の語 `cocartesian covariant fiberwise functor hom homotopy internal precomposition relative transport`。普通圏の語 `contravariant fiberwise functor hom homotopy internal postcomposition pullback relative transport`。確認した候補 `homotopyTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:30`), `homotopyTransport_map_isTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:68`), `markedCocartesianFunctorSpace` (`SerrePositivity/InfinityCategories/F1/Cocartesian/MarkedCocartesianFunctorSpace.lean:38`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Simplicial`, `SerrePositivity/InfinityCategories/F1B/CocartesianScaffold`, `SerrePositivity/InfinityCategories/F1B/Fibrations` を検索。対象の宣言見出し 617 件。

### [5.3.7.3](https://kerodon.net/tag/0478) · `none → partial`（partial_kind: `special`）

前者は x→G(y) のモデルの inner 性。後者を K=Δ⁰ とすると矢印圏の始域射影に関する (2) の十分条件に当たる。任意の二射への引戻し・両射影の fibration 性・必要条件は未確認。

- (a) `5.3.7.3` と `5.3.7`、`Kerodon`。直接 0 件、同小節 44 件。参照例 `SerrePositivity/InfinityCategories/Core/ConeFirstVertex.lean:6`, `SerrePositivity/InfinityCategories/Core/InitialHornProductBoundary.lean:6`。
- (b) `oriented fiber product cartesian projection / comma cocartesian target / arrow pullback cartesian edge`。双対の語 `arrow cartesian cocartesian comma coproduct edge fiber oriented projection pushout target`。普通圏の語 `arrow cocartesian comma edge fiber fibre oriented product projection pullback target`。確認した候補 `unitCommaSource_innerFibration` (`SerrePositivity/InfinityCategories/F1B/Adjunction/UnitComma.lean:77`), `isCartesianEdge_coconeRestriction_of_apex` (`SerrePositivity/InfinityCategories/F1/CoconeRestrictionCartesianEdge.lean:39`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1B/Fibrations`, `SerrePositivity/InfinityCategories/Stable` を検索。対象の宣言見出し 4663 件。

### [5.3.8.10](https://kerodon.net/tag/05PX) · `none → none`

同型移送や頂点ファイバーの同型のみ。全ての Δⁿ 上の積への自明化と minimal Kan fibration の同値には minimal 性が必要。

- (a) `5.3.8.10` と `5.3.8`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `minimal Kan fibration simplex trivialization / minimal simplicial pullback product / fiberwise minimal`。双対の語 `coproduct fiberwise fibration kan minimal pushout simplex simplicial trivialization`。普通圏の語 `fiberwise kan lifting minimal product pullback simplex simplicial trivialization`。確認した候補 `Nonsingular.of_iso` (`Mathlib/AlgebraicTopology/SimplicialSet/Nonsingular.lean:67`), `weightedNerveFiberIso` (`SerrePositivity/InfinityCategories/F1/Weighted/NerveFiber.lean:123`)。
- (c) 候補を起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet`, `SerrePositivity/InfinityCategories/F1/Weighted` を検索。対象の宣言見出し 1491 件。

### [5.4.1.1](https://kerodon.net/tag/01W9) · `none → none`

前者は豊穣圏、後者は辺を固定した相対ホーン。thin 2 単体の公理と両端の退化条件を持つ構造がない。

- (a) `5.4.1.1` と `5.4.1`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `infinity bicategory axioms thin simplex / scaled simplicial set / outer horn left degenerate`。双対の語 `axioms bicategory degenerate horn infinity outer right scaled set simplex simplicial thin`。普通圏の語 `axioms bicategory degenerate horn infinity left outer scaled set simplex simplicial thin`。確認した候補 `quasicategoryObject_simplicialCategory` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:60`), `IsCocartesianEdge` (`SerrePositivity/InfinityCategories/F1/Fibrations/CartesianEdge.lean:34`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 666 件。

### [5.4.1.2](https://kerodon.net/tag/01WA) · `none → none`

準圏の豊穣圏とその core Hom を用いた nerve の準圏性。任意の準圏を thin 単体付き ∞ 双圏にする型は確認できない。

- (a) `5.4.1.2` と `5.4.1`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `quasicategory infinity bicategory / thin triangle all / scaled simplicial nerve`。双対の語 `bicategory infinity nerve quasicategory scaled simplicial thin triangle`。普通圏の語 `bicategory coherent infinity nerve quasicategory scaled simplicial thin triangle`。確認した候補 `quasicategoryObject_simplicialCategory` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:60`), `catInfinity_quasicategory` (`SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean:30`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 372 件。

### [5.4.2.9](https://kerodon.net/tag/01WQ) · `none → none`

inner fibration の合成は一般に可能だが、thin 単体を含む interior fibration の lift と保存の結論を持たない。

- (a) `5.4.2.9` と `5.4.2`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `interior fibration composition / scaled fibration composite / thin preservation inner`。双対の語 `composite composition fibration inner interior preservation scaled thin`。普通圏の語 `composite composition inner interior lifting preservation scaled thin`。確認した候補 `innerFibrations` (`Mathlib/AlgebraicTopology/Quasicategory/InnerFibration.lean:66`), `unitCommaPair_innerFibration` (`SerrePositivity/InfinityCategories/F1B/Adjunction/UnitComma.lean:69`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/Quasicategory`, `SerrePositivity/InfinityCategories/Core` を検索。対象の宣言見出し 2394 件。

### [5.4.3.11](https://kerodon.net/tag/01X5) · `none → none`

前者は特定の部分複体の制限、後者は通常の準圏での apex 可逆条件。K₀ の各点の thin 三角を K の全点で thin な lift にする結論がない。

- (a) `5.4.3.11` と `5.4.3`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `thin slice restriction lift / interior fibration cartesian over diagram / scaled lifting edge`。双対の語 `cocartesian coslice diagram edge fibration interior lift lifting restriction scaled thin under`。普通圏の語 `diagram edge interior lift lifting over pullback restriction scaled slice thin`。確認した候補 `sliceUnderRestrict_trivialKanFibration_subcomplexIso` (`SerrePositivity/InfinityCategories/F1/Joins/CosliceRightRestriction.lean:78`), `isCartesianEdge_coconeRestriction_of_apex` (`SerrePositivity/InfinityCategories/F1/CoconeRestrictionCartesianEdge.lean:39`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/Core` を検索。対象の宣言見出し 2340 件。

### [5.4.4.1](https://kerodon.net/tag/01X8) · `none → partial`（partial_kind: `special`）

準圏を全 2 単体が thin の場合として見ると、点 slice/coslice の各辺が cartesian/cocartesian になる大域条件 (2),(4) を直接得る。一般の ∞ 双圏の thin 判定と局所条件は未確認。

- (a) `5.4.4.1` と `5.4.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `thin triangle slice cartesian / coslice cocartesian left fibration / right fibration all edges`。双対の語 `cartesian cocartesian coslice edges fibration left right slice thin triangle`。普通圏の語 `cocartesian coslice edges left lifting pullback right slice thin triangle`。確認した候補 `isCartesianEdge_of_rightFibration` (`SerrePositivity/InfinityCategories/F1/Fibrations/CartesianEdge.lean:44`), `isCocartesianEdge_of_leftFibration` (`SerrePositivity/InfinityCategories/F1/Fibrations/CartesianEdge.lean:57`), `sliceOverProjection_rightFibration` (`SerrePositivity/InfinityCategories/Core/RightFibration.lean:211`), `sliceUnderProjection_leftFibration` (`SerrePositivity/InfinityCategories/Core/RightFibration.lean:318`)。
- (c) 候補を起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 2634 件。

### [5.4.5.7](https://kerodon.net/tag/01XH) · `none → none`

候補は一つの 2 単体の辺に関する閉性。任意の 2 単体集合と四面体の四つの面に関する指定の iff は確認できない。

- (a) `5.4.5.7` と `5.4.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `inner exchange thin tetrahedron / scaled simplex exchange / thin two out of four`。双対の語 `exchange four inner out scaled simplex tetrahedron thin two`。普通圏の語 `exchange four inner out scaled simplex tetrahedron thin two`。確認した候補 `isCocartesianEdge_triangle_longEdge` (`SerrePositivity/InfinityCategories/F1/Cocartesian/Composition.lean:23`), `localEquivalences_compStruct` (`SerrePositivity/InfinityCategories/HomotopyLimits/Presentable/LocalEquivalenceTriangles.lean:46`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory/Bicategory` を検索。対象の宣言見出し 368 件。

### [5.4.9.1](https://kerodon.net/tag/02RY) · `none → none`

輸送の一般構成と空間の pointed projection の頂点同定。任意の局所 Kan 豊穣圏で hC 上の Hom(X,-) と指定輸送の自然同型を得ない。

- (a) `5.4.9.1` と `5.4.9`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `enriched Yoneda homotopy transport representable / coherent nerve coslice transport / homotopy category Kan representable`。双対の語 `category coherent enriched homotopy kan nerve representable slice transport yoneda`。普通圏の語 `category coherent coslice enriched homotopy kan nerve transport yoneda`。確認した候補 `homotopyTransport` (`SerrePositivity/InfinityCategories/F1/Transport/HomotopyTransport.lean:30`), `pointedSpaceFiberVertexEquiv` (`SerrePositivity/InfinityCategories/F1/StraighteningLeft/PointedSpaceFiberVertices.lean:25`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Coherent` を検索。対象の宣言見出し 953 件。

### [5.5.1.21](https://kerodon.net/tag/01ZS) · `none → none`

点付き空間は最初から coherent nerve の coslice。任意の局所 Kan 豊穣圏について、豊穣 coslice の nerve からの c' やその同値を確認できない。

- (a) `5.5.1.21` と `5.5.1`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `simplicial enriched coslice comparison / coherent nerve coslice equivalence / precomposition Kan fibration`。双対の語 `coherent comparison enriched equivalence fibration kan nerve postcomposition simplicial slice`。普通圏の語 `coherent comparison coslice enriched equivalence kan lifting nerve precomposition simplicial`。確認した候補 `PointedSpaceInfinity` (`SerrePositivity/InfinityCategories/F1/Categories/PointedSpaces.lean:60`), `quasicategoryObject_enrichedCategory` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:48`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory/Comma/Over`, `Mathlib/CategoryTheory/WithTerminal`, `SerrePositivity/InfinityCategories/HomotopyLimits` を検索。対象の宣言見出し 5454 件。

### [5.5.1.22](https://kerodon.net/tag/01ZT) · `none → none`

豊穣圏の構成と strict transport の全忠実性。豊穣 coslice の部分圏 E に制限した c' の全忠実性は別。

- (a) `5.5.1.22` と `5.5.1`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `full enriched coslice fully faithful / coherent nerve comparison full subcategory / precomposition Kan fibration`。双対の語 `coherent comparison enriched faithful fibration full fully kan nerve postcomposition slice subcategory`。普通圏の語 `coherent comparison coslice enriched faithful full fully kan lifting nerve precomposition subcategory`。確認した候補 `quasicategoryObject_simplicialCategory` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:60`), `cocartesianStrictTransportInfinityMap_isFullyFaithful` (`SerrePositivity/InfinityCategories/F1/Cocartesian/StrictTransportEnriched.lean:52`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory/Comma/Over`, `Mathlib/CategoryTheory/WithTerminal`, `SerrePositivity/InfinityCategories/HomotopyLimits` を検索。対象の宣言見出し 5454 件。

### [5.5.3.16](https://kerodon.net/tag/06T6) · `none → none`

QC の準圏性、全忠実な比較は確認。QC 内の mono と、同型を含む mapping space の成分、replete subcategory への同値の対応を確認できない。

- (a) `5.5.3.16` と `5.5.3`、`Kerodon`。直接 0 件、同小節 35 件。参照例 `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:7`, `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:11`。
- (b) `cat infinity monomorphism replete / fully faithful summand mapping space / mono QC essential image`。双対の語 `cat epi essential faithful fully image infinity mapping monomorphism qc replete space summand`。普通圏の語 `cat essential faithful fully image infinity mapping mono monomorphism qc replete space summand`。確認した候補 `catInfinity_quasicategory` (`SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean:30`), `isFullyFaithful_of_trivialKanFibration` (`SerrePositivity/InfinityCategories/Core/MappingSpaceTrivialFibration.lean:94`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 372 件。

### [5.5.3.19](https://kerodon.net/tag/06T7) · `none → none`

関手 Hom と core の Kan 性まではある。両方の次数 n の切断性と QC の対象としての切断性との iff はない。

- (a) `5.5.3.19` と `5.5.3`、`Kerodon`。直接 0 件、同小節 35 件。参照例 `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:7`, `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:11`。
- (b) `cat infinity truncated object / locally truncated core Kan / QC truncation`。双対の語 `cat core infinity kan locally object qc truncated truncation`。普通圏の語 `cat core infinity kan locally object qc truncated truncation`。確認した候補 `qCat_sHom_kanComplex` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:99`), `quasicategoryCore_kanComplex` (`SerrePositivity/InfinityCategories/F1/Categories/CoreKan.lean:61`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 372 件。

### [5.5.3.21](https://kerodon.net/tag/05EW) · `none → none`

候補は Hom が Kan で QC が準圏になること。n の切断から局所性、または局所 n−1 から QC の n 切断を与えない。

- (a) `5.5.3.21` と `5.5.3`、`Kerodon`。直接 0 件、同小節 35 件。参照例 `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:7`, `SerrePositivity/InfinityCategories/F1/CatInfinity/CoherentVertices.lean:11`。
- (b) `cat infinity truncation shift / locally n truncated / QC object truncated`。双対の語 `cat infinity locally object qc shift truncated truncation`。普通圏の語 `cat infinity locally object qc shift truncated truncation`。確認した候補 `qCat_sHom_kanComplex` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:99`), `catInfinity_quasicategory` (`SerrePositivity/InfinityCategories/F1/Categories/CatInfinity.lean:30`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 372 件。

### [5.5.5.9](https://kerodon.net/tag/0211) · `none → none`

空間または準圏の通常 coslice の左 fibration と豊穣圏構造。core を取る前の QC 上の対象分類射と interior fibration 性は確認できない。

- (a) `5.5.5.9` と `5.5.5`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `object classifier infinity bicategory interior fibration / pointed quasicategory simplicial nerve / scaled QC Obj`。双対の語 `bicategory classifier fibration infinity interior nerve obj object pointed qc quasicategory scaled simplicial`。普通圏の語 `bicategory classifier coherent infinity interior lifting nerve obj object pointed qc quasicategory scaled simplicial`。確認した候補 `pointedSpaceProjection` (`SerrePositivity/InfinityCategories/F1/Categories/PointedSpaces.lean:67`), `sliceUnderProjection_leftFibration` (`SerrePositivity/InfinityCategories/Core/RightFibration.lean:318`), `quasicategoryObject_simplicialCategory` (`SerrePositivity/InfinityCategories/F1/Categories/QCatSimplicial.lean:60`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1/Categories`, `SerrePositivity/InfinityCategories/F1/Coherent` を検索。対象の宣言見出し 3665 件。

### [5.6.3.4](https://kerodon.net/tag/0276) · `none → none`

普通圏の擬関手の Grothendieck 構成と重み付き nerve の係数ファイバー同型。Duskin nerve による全空間 T の同型は確認できない。

- (a) `5.6.3.4` と `5.6.3`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `Duskin nerve Grothendieck comparison / unstraightening category Grothendieck nerve iso / strictly unital pseudofunctor`。双対の語 `category comparison duskin grothendieck iso nerve pseudofunctor strictly unital unstraightening`。普通圏の語 `category coherent comparison duskin grothendieck iso nerve pseudofunctor strictly unital unstraightening`。確認した候補 `category` (`Mathlib/CategoryTheory/Bicategory/Grothendieck.lean:139`), `weightedNerveFiberIso` (`SerrePositivity/InfinityCategories/F1/Weighted/NerveFiber.lean:123`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory` を検索。対象の宣言見出し 1708 件。

## 照合に使った kernel 型

段1・段1′と対象章の kernel evidence にある型。表示用に空白を整えた。

### 5.1.1.10

```lean
@SerrePositivity.InfinityCategories.isCocartesianEdge_constant.{u_1} : ∀ {X B : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] [SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} X B) [SSet.InnerFibration.{u_1} p] (x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })), SerrePositivity.InfinityCategories.IsCocartesianEdge.{u_1} p (SerrePositivity.InfinityCategories.PinchedHom.constant.{u_1} x 1)
@SerrePositivity.InfinityCategories.isCartesianEdge_of_isInvertibleEdge.{u_1} : ∀ {X B : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] [SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} X B) [SSet.InnerFibration.{u_1} p] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} (e : SSet.Truncated.Edge.{u_1} x y), SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} e → SerrePositivity.InfinityCategories.IsCartesianEdge.{u_1} p (SSet.Truncated.Edge.edge.{u_1} e)
```

### 5.1.4.1

```lean
@SerrePositivity.InfinityCategories.CartesianFibration.{u_1} : {X B : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X B → Prop
SerrePositivity.InfinityCategories.cartesianFibrations.{u_1} : CategoryTheory.MorphismProperty.{u_1, u_1 + 1} SSet.{u_1}
@SerrePositivity.InfinityCategories.CocartesianFibration.{u_1} : {X B : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X B → Prop
@SerrePositivity.InfinityCategories.CocartesianHornFibration.{u_1} : {E B : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} E B → Prop
```

### 5.2.3.11

```lean
@SerrePositivity.InfinityCategories.relativeJoin_quasicategory.{u_1} : ∀ {X Y S : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] [SSet.Quasicategory.{u_1} Y] [SSet.Quasicategory.{u_1} S] (f : Quiver.Hom.{u_1, u_1 + 1} X S) (g : Quiver.Hom.{u_1, u_1 + 1} Y S), SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.relativeJoin.{u_1} f g)
@SerrePositivity.InfinityCategories.relativeJoinProjection_innerFibration.{u_1} : ∀ {X Y S : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] [SSet.Quasicategory.{u_1} Y] [SSet.Quasicategory.{u_1} S] (f : Quiver.Hom.{u_1, u_1 + 1} X S) (g : Quiver.Hom.{u_1, u_1 + 1} Y S), SSet.InnerFibration.{u_1} (SerrePositivity.InfinityCategories.relativeJoinProjection.{u_1} f g)
```

### 5.2.4.5

```lean
@SerrePositivity.InfinityCategories.isPrecompositionEquivalence_relativeJoinCylinderComparison.{u_1} : ∀ {X Y : SSet.{u_1}} (f : Quiver.Hom.{u_1, u_1 + 1} X Y), SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.relativeJoinCylinderComparison.{u_1} f)
@SerrePositivity.InfinityCategories.relativeJoinCylinderComparison.{u_1} : {X Y : SSet.{u_1}} → (f : Quiver.Hom.{u_1, u_1 + 1} X Y) → Quiver.Hom.{u_1, u_1 + 1} (CategoryTheory.Limits.pushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 X) f) (SerrePositivity.InfinityCategories.relativeJoin.{u_1} f (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} Y))
```

### 5.2.6.2

```lean
@CategoryTheory.Functor.Elements.costructuredArrowYonedaEquivalence.{u_1, u_2} : {C : Type u_2} → [inst : CategoryTheory.Category.{u_1, u_2} C] → (F : @CategoryTheory.Functor.{u_1, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) (Type u_1) CategoryTheory.types.{u_1}) → @CategoryTheory.Equivalence.{u_1, u_1, max u_2 u_1, max u_2 u_1} (Opposite.{max (u_2 + 1) (u_1 + 1)} (@CategoryTheory.Functor.Elements.{u_1, u_1, u_2} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) F)) (@CategoryTheory.CostructuredArrow.{u_1, max u_2 u_1, u_2, max u_2 (u_1 + 1)} C inst (@CategoryTheory.Functor.{u_1, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.Functor.category.{u_1, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.yoneda.{u_1, u_2} C inst) F) (@CategoryTheory.Category.opposite.{u_1, max u_2 u_1} (@CategoryTheory.Functor.Elements.{u_1, u_1, u_2} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) F) (@CategoryTheory.Functor.Elements.instCategory.{u_1, u_1, u_2} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) F)) (@CategoryTheory.instCategoryCostructuredArrow.{u_1, max u_2 u_1, u_2, max u_2 (u_1 + 1)} C inst (@CategoryTheory.Functor.{u_1, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.Functor.category.{u_1, u_1, u_2, u_1 + 1} (Opposite.{u_2 + 1} C) (@CategoryTheory.Category.opposite.{u_1, u_2} C inst) (Type u_1) CategoryTheory.types.{u_1}) (@CategoryTheory.yoneda.{u_1, u_2} C inst) F)
```

### 5.3.1.10

```lean
@SerrePositivity.InfinityCategories.cocartesianRelativeFunctorSpace.{u_1} : {E F B : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} E B → Quiver.Hom.{u_1, u_1 + 1} F B → SSet.{u_1}
@SerrePositivity.InfinityCategories.cocartesianRelativeFunctorPredicate.{u_1} : {E F B : SSet.{u_1}} → (p : Quiver.Hom.{u_1, u_1 + 1} E B) → (q : Quiver.Hom.{u_1, u_1 + 1} F B) → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.relativeFunctorSpace.{u_1} q p) (Opposite.op.{1} { len := 0 }) → Prop
```

### 5.3.2.3

```lean
@SerrePositivity.InfinityCategories.simplicialReplacementBaseMap.{u_1} : {C D : Type u_1} → [inst : CategoryTheory.Category.{u_1, u_1} C] → [inst_1 : CategoryTheory.Category.{u_1, u_1} D] → (H : CategoryTheory.Functor.{u_1, u_1, u_1, u_1} D C) → (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplicialReplacement.{u_1} (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1 + 1} H F)) (SerrePositivity.InfinityCategories.simplicialReplacement.{u_1} F)
@SerrePositivity.InfinityCategories.simplicialReplacementBaseMap_isPullback.{u_1} : ∀ {C D : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] [inst_1 : CategoryTheory.Category.{u_1, u_1} D] (H : CategoryTheory.Functor.{u_1, u_1, u_1, u_1} D C) (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}), CategoryTheory.IsPullback.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplicialReplacementBaseMap.{u_1} H F) (SerrePositivity.InfinityCategories.simplicialReplacementProjection.{u_1} (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1 + 1} H F)) (SerrePositivity.InfinityCategories.simplicialReplacementProjection.{u_1} F) (CategoryTheory.nerveMap.{u_1, u_1} H)
```

### 5.3.2.11

```lean
@SerrePositivity.InfinityCategories.simplicialReplacement.{u_1} : {C : Type u_1} → [inst : CategoryTheory.Category.{u_1, u_1} C] → CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1} → SSet.{u_1}
```

### 5.3.2.13

```lean
SerrePositivity.InfinityCategories.simplicialReplacementIntervalIso.{u_1} : (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} (ULift.{u_1, 0} (Fin 2)) SSet.{u_1}) → CategoryTheory.Iso.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplicialReplacement.{u_1} F) (CategoryTheory.Limits.pushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F (ULift.up.{u_1, 0} 0))) (SerrePositivity.InfinityCategories.scaffoldIntervalMap.{u_1} F))
SerrePositivity.InfinityCategories.scaffoldInterval_isPushout.{u_1} : ∀ (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} (ULift.{u_1, 0} (Fin 2)) SSet.{u_1}), CategoryTheory.IsPushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.prismEndpoint.{u_1} 1 (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F (ULift.up.{u_1, 0} 0))) (SerrePositivity.InfinityCategories.scaffoldIntervalMap.{u_1} F) (SerrePositivity.InfinityCategories.scaffoldIntervalPrism.{u_1} F) (SerrePositivity.InfinityCategories.simplicialReplacementConstantLift.{u_1} F (ULift.up.{u_1, 0} 1))
```

### 5.3.4.11

```lean
@SerrePositivity.InfinityCategories.tautScaffold.{u_1} : {C : Type u_1} → [inst : CategoryTheory.Category.{u_1, u_1} C] → (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplicialReplacement.{u_1} F) (SerrePositivity.InfinityCategories.weightedNerve.{u_1} F)
@SerrePositivity.InfinityCategories.tautScaffoldDiagram.{u_1} : {C : Type u_1} → [inst : CategoryTheory.Category.{u_1, u_1} C] → (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) → {n : ℕ} → (s : SerrePositivity.InfinityCategories.simplicialReplacementSimplex.{u_1} F n) → Quiver.Hom.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplexPrefixWeight.{u_1} n) (CategoryTheory.Functor.comp.{0, u_1, u_1, 0, u_1, u_1 + 1} (Sigma.fst.{u_1, u_1} s) F)
```

### 5.3.4.12

```lean
@SerrePositivity.InfinityCategories.tautScaffold_projection.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}), Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.tautScaffold.{u_1} F) (SerrePositivity.InfinityCategories.weightedNerveProjection.{u_1} F)) (SerrePositivity.InfinityCategories.simplicialReplacementProjection.{u_1} F)
```

### 5.3.4.14

```lean
@SerrePositivity.InfinityCategories.tautScaffold_map.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] {F G : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}} (η : Quiver.Hom.{u_1, u_1 + 1} F G), Eq.{u_1 + 1} (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.simplicialReplacementMap.{u_1} η) (SerrePositivity.InfinityCategories.tautScaffold.{u_1} G)) (CategoryTheory.CategoryStruct.comp.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.tautScaffold.{u_1} F) (SerrePositivity.InfinityCategories.weightedNerveMap.{u_1} η))
@SerrePositivity.InfinityCategories.tautScaffold_baseMap_isPullback.{u_1} : ∀ {C D : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] [inst_1 : CategoryTheory.Category.{u_1, u_1} D] (H : CategoryTheory.Functor.{u_1, u_1, u_1, u_1} D C) (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}), CategoryTheory.IsPullback.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.tautScaffold.{u_1} (CategoryTheory.Functor.comp.{u_1, u_1, u_1, u_1, u_1, u_1 + 1} H F)) (SerrePositivity.InfinityCategories.simplicialReplacementBaseMap.{u_1} H F) (SerrePositivity.InfinityCategories.weightedNerveBaseMap.{u_1} H F) (SerrePositivity.InfinityCategories.tautScaffold.{u_1} F)
```

### 5.3.4.17

```lean
@SerrePositivity.InfinityCategories.tautScaffold_isCocartesianScaffold.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) [inst_1 : ∀ (c : C), SSet.Quasicategory.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F c)], SerrePositivity.InfinityCategories.CocartesianScaffold.{u_1} (SerrePositivity.InfinityCategories.weightedNerveProjection.{u_1} F) F (SerrePositivity.InfinityCategories.tautScaffold.{u_1} F)
@SerrePositivity.InfinityCategories.tautScaffold_isLeftScaffold.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) [inst_1 : ∀ (c : C), SSet.KanComplex.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F c)], SerrePositivity.InfinityCategories.IsLeftScaffold.{u_1} (SerrePositivity.InfinityCategories.weightedNerveProjection.{u_1} F) F (SerrePositivity.InfinityCategories.tautScaffold.{u_1} F)
```

### 5.3.4.19

```lean
@SerrePositivity.InfinityCategories.weightedNerveCocartesianTransportUnit.{u_1} : {C : Type u_1} → [inst : CategoryTheory.Category.{u_1, u_1} C] → (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) → [∀ (c : C), SSet.Quasicategory.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F c)] → Quiver.Hom.{u_1, u_1 + 1} F (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram.{u_1} (SerrePositivity.InfinityCategories.weightedNerveProjection.{u_1} F))
@SerrePositivity.InfinityCategories.weightedNerveCocartesianTransportUnit_isQCatEquivalence.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] (F : CategoryTheory.Functor.{u_1, u_1, u_1, u_1 + 1} C SSet.{u_1}) [inst_1 : ∀ (c : C), SSet.Quasicategory.{u_1} (CategoryTheory.Functor.obj.{u_1, u_1, u_1, u_1 + 1} F c)] (c : C), SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} (CategoryTheory.NatTrans.app.{u_1, u_1, u_1, u_1 + 1} (SerrePositivity.InfinityCategories.weightedNerveCocartesianTransportUnit.{u_1} F) c)
```

### 5.3.5.12

```lean
@SerrePositivity.InfinityCategories.cocartesianStrictTransportMappingSpaceMap_isQCatEquivalence.{u_1} : ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_1, u_1} C] {E D : SSet.{u_1}} (p : Quiver.Hom.{u_1, u_1 + 1} E (CategoryTheory.nerve.{u_1, u_1} C)) (q : Quiver.Hom.{u_1, u_1 + 1} D (CategoryTheory.nerve.{u_1, u_1} C)) [SerrePositivity.InfinityCategories.CocartesianFibration.{u_1} p] [inst_2 : SerrePositivity.InfinityCategories.CocartesianFibration.{u_1} q], SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} (SerrePositivity.InfinityCategories.cocartesianStrictTransportMappingSpaceMap.{u_1} p q)
SerrePositivity.InfinityCategories.cocartesianStrictTransportInfinityMap_isFullyFaithful.{u_1} : ∀ (C : Type u_1) [inst : CategoryTheory.Category.{u_1, u_1} C], SerrePositivity.InfinityCategories.IsFullyFaithful.{u_1 + 1} (SerrePositivity.InfinityCategories.cocartesianStrictTransportInfinityMap.{u_1} C)
```

### 5.5.2.1

```lean
SerrePositivity.InfinityCategories.PointedSpaceInfinity.{u_1} : SSet.{u_1 + 1}
SerrePositivity.InfinityCategories.pointedSpaceFiberVertexEquiv.{u_1} : (K : SerrePositivity.InfinityCategories.KanObject.{u_1}) → Equiv.{u_1 + 2, u_1 + 1} (CategoryTheory.Functor.obj.{0, u_1 + 1, 0, u_1 + 2} (SerrePositivity.InfinityCategories.vertexFiber.{u_1 + 1} SerrePositivity.InfinityCategories.pointedSpaceProjection.{u_1} (SerrePositivity.InfinityCategories.spaceInfinityVertex.{u_1} K)) (Opposite.op.{1} { len := 0 })) (CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.KanObject.obj.{u_1} K) (Opposite.op.{1} { len := 0 }))
SerrePositivity.InfinityCategories.SpaceInfinity.{u_1} : SSet.{u_1 + 1}
```

### 5.5.3.3

```lean
SerrePositivity.InfinityCategories.catInfinity_quasicategory.{u_1} : SSet.Quasicategory.{u_1 + 1} SerrePositivity.InfinityCategories.CatInfinity.{u_1}
SerrePositivity.InfinityCategories.quasicategoryCore_kanComplex.{u_1} : ∀ (X : SSet.{u_1}) [SSet.Quasicategory.{u_1} X], SSet.KanComplex.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.quasicategoryCore.{u_1} X))
SerrePositivity.InfinityCategories.qCat_sHom_kanComplex.{u_1} : ∀ (X Y : SerrePositivity.InfinityCategories.QCat.{u_1}), SSet.KanComplex.{u_1} (CategoryTheory.SimplicialCategory.sHom.{u_1, u_1 + 1} X Y)
```

### 5.5.4.1

```lean
SerrePositivity.InfinityCategories.QuasicategoryObject.{u_1} : Type (u_1 + 1)
SerrePositivity.InfinityCategories.quasicategoryObject_enrichedCategory.{u_1} : CategoryTheory.EnrichedCategory.{u_1, u_1 + 1, u_1 + 1} SSet.{u_1} SerrePositivity.InfinityCategories.QuasicategoryObject.{u_1}
SerrePositivity.InfinityCategories.quasicategoryObject_simplicialCategory.{u_1} : CategoryTheory.SimplicialCategory.{u_1, u_1 + 1} SerrePositivity.InfinityCategories.QuasicategoryObject.{u_1}
CategoryTheory.SimplicialNerve.{u_1, u_2} : (C : Type u_2) → [inst : CategoryTheory.Category.{u_1, u_2} C] → [CategoryTheory.SimplicialCategory.{u_1, u_2} C] → SSet.{max u_2 u_1}
```

### 5.6.1.1

```lean
@CategoryTheory.Pseudofunctor.Grothendieck.{u_1, u_2, u_3, u_4} : {𝒮 : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} 𝒮] → @CategoryTheory.Pseudofunctor.{u_1, max u_4 u_2, u_1, max u_4 u_2, u_3, max (u_4 + 1) (u_2 + 1)} (CategoryTheory.LocallyDiscrete.{u_3} 𝒮) (@CategoryTheory.locallyDiscreteBicategory.{u_1, u_3} 𝒮 inst) CategoryTheory.Cat.{u_2, u_4} CategoryTheory.Cat.bicategory.{u_2, u_4} → Type (max u_3 u_4)
@CategoryTheory.Pseudofunctor.Grothendieck.category.{u_1, u_2, u_3, u_4} : {𝒮 : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} 𝒮] → {F : @CategoryTheory.Pseudofunctor.{u_1, max u_4 u_2, u_1, max u_4 u_2, u_3, max (u_4 + 1) (u_2 + 1)} (CategoryTheory.LocallyDiscrete.{u_3} 𝒮) (@CategoryTheory.locallyDiscreteBicategory.{u_1, u_3} 𝒮 inst) CategoryTheory.Cat.{u_2, u_4} CategoryTheory.Cat.bicategory.{u_2, u_4}} → CategoryTheory.Category.{max u_1 u_2, max u_4 u_3} (@CategoryTheory.Pseudofunctor.Grothendieck.{u_1, u_2, u_3, u_4} 𝒮 inst F)
@CategoryTheory.Grothendieck.{u_1, u_2, u_3, u_4} : {C : Type u_1} → [inst : CategoryTheory.Category.{u_2, u_1} C] → @CategoryTheory.Functor.{u_2, max u_3 u_4, u_1, max (u_3 + 1) (u_4 + 1)} C inst CategoryTheory.Cat.{u_4, u_3} CategoryTheory.Cat.category.{u_4, u_3} → Type (max u_1 u_3)
```

### 5.6.1.5

```lean
@CategoryTheory.Pseudofunctor.CoGrothendieck.{u_1, u_2, u_3, u_4} : {𝒮 : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} 𝒮] → @CategoryTheory.Pseudofunctor.{u_1, max u_4 u_2, u_1, max u_4 u_2, u_3, max (u_4 + 1) (u_2 + 1)} (CategoryTheory.LocallyDiscrete.{u_3} (Opposite.{u_3 + 1} 𝒮)) (@CategoryTheory.locallyDiscreteBicategory.{u_1, u_3} (Opposite.{u_3 + 1} 𝒮) (@CategoryTheory.Category.opposite.{u_1, u_3} 𝒮 inst)) CategoryTheory.Cat.{u_2, u_4} CategoryTheory.Cat.bicategory.{u_2, u_4} → Type (max u_3 u_4)
@CategoryTheory.Pseudofunctor.CoGrothendieck.category.{u_1, u_2, u_3, u_4} : {𝒮 : Type u_3} → [inst : CategoryTheory.Category.{u_1, u_3} 𝒮] → {F : @CategoryTheory.Pseudofunctor.{u_1, max u_4 u_2, u_1, max u_4 u_2, u_3, max (u_4 + 1) (u_2 + 1)} (CategoryTheory.LocallyDiscrete.{u_3} (Opposite.{u_3 + 1} 𝒮)) (@CategoryTheory.locallyDiscreteBicategory.{u_1, u_3} (Opposite.{u_3 + 1} 𝒮) (@CategoryTheory.Category.opposite.{u_1, u_3} 𝒮 inst)) CategoryTheory.Cat.{u_2, u_4} CategoryTheory.Cat.bicategory.{u_2, u_4}} → CategoryTheory.Category.{max u_1 u_2, max u_4 u_3} (@CategoryTheory.Pseudofunctor.CoGrothendieck.{u_1, u_2, u_3, u_4} 𝒮 inst F)
```
