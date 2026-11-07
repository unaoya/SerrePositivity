# 第4章の交差抜き取り検査（research/kerodon-review-c）

- 対象は main の `dc3ebc8ab`。依頼に従い第4〜6章を選んだ。既存の同名の抜き取り報告と区別するため、ファイル名に `-c` を付けた。
- 乱数の種は `0x81e593fc`。Python 3.14.7 の `random.Random(seed).sample` で、章を 4→5→6、区分を own・both・mathlib の合算→none の順に処理した。各母集団は項目番号の数値順、各区分は重複なしの20件。
- 元表の status と引用で抽出・型の取得を行い、Kerodon 本文、段1・段1′と章別 kernel evidence の型、Lean ソースから判定した。元表の reason は判定に使っていない。
- none では (a) 元の citations.csv と Lean docstring の該当番号・同小節の引用、(b) 宣言名と型の語索引を原方向・双対・普通圏の語で検索、(c) 同小節の own・both の引用ファイルと同じディレクトリの宣言を検索した。近傍は起点がなければ mathlib・partial、同小節の引用、候補の順で補った。候補の採否は各行の型・ソースとの照合による。
- 差は status の変更で数えた。§8.1 に従い、特例・一方向・強い仮定・複数結論の一部が直接確認できる場合を partial とした。

| 元の区分 | 母集団 | 抽出 | 差 | 差の割合 |
|---|---:|---:|---:|---:|
| own・both・mathlib | 134 | 20 | 0 | 0% |
| none | 187 | 20 | 4 | 20% |

## own・both・mathlib

| Kerodon | 元の status | 照合結果 | 仮定・結論と確認した宣言 |
|---|---|---|---|
| [4.2.1.1](https://kerodon.net/tag/00T9) | own | own | 任意の単体集合の射に対する LeftFibration と RightFibration。クラスの mem はそれぞれ i<n と 0<i の内外ホーンの右持ち上げを量化しており、両向きの定義が一致する。 `SerrePositivity.InfinityCategories.LeftFibration` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:48), `SerrePositivity.InfinityCategories.RightFibration` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:41), `SerrePositivity.InfinityCategories.leftFibrations` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:34) |
| [4.2.5.3](https://kerodon.net/tag/0153) | own | own | 左アノダインの pushout product は第一変数の場合を直接カバーする。右アノダインは同じ二変数を交換する対称性を用いる形で、同じ pushout product の右アノダイン性に対応する。第一変数の cofinalRightAnodyne_pushoutObjObj_left もソースで確認した。 `SerrePositivity.InfinityCategories.leftAnodyneExtensions_pushoutObjObj_left` (SerrePositivity/InfinityCategories/F1/Fibrations/LeftAnodynePushoutProduct.lean:60), `SerrePositivity.InfinityCategories.leftAnodyneExtensions_pushoutObjObj_right` (SerrePositivity/InfinityCategories/F1/Fibrations/LeftAnodynePushoutProduct.lean:46), `SerrePositivity.InfinityCategories.cofinalRightAnodyne_pushoutObjObj_right` (SerrePositivity/InfinityCategories/F1B/Fibrations/RightAnodyneTensor.lean:147) |
| [4.3.3.1](https://kerodon.net/tag/016L) | mathlib | mathlib | IsLowerSet は任意の前順序の下方閉部分集合を定義する。Kerodon の線形順序への特殊化が initial segment の条件に一致する。 `IsLowerSet` (Mathlib/Order/Defs/Unbundled.lean:280) |
| [4.3.6.1](https://kerodon.net/tag/018F) | own | own | 同じ任意の図式と準圏に対する二つの slice 射影は左・右ファイブレーション。基底が準圏なら内ファイブレーションの始域が準圏になり、両 slice の準圏性も得る。 `SerrePositivity.InfinityCategories.sliceOverProjection_rightFibration` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:211), `SerrePositivity.InfinityCategories.sliceUnderProjection_leftFibration` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:318), `SerrePositivity.InfinityCategories.sliceOver_quasicategory` (SerrePositivity/InfinityCategories/Core/RightFibration.lean:223) |
| [4.3.6.3](https://kerodon.net/tag/018H) | own | own | 単射を像の部分複体として取ると、joinUnion は二つの指定 join の和で、joinUnion_isPushout がその交差を共通の join とする。余域への射は部分複体の包含で原文の pushout-join に一致する。 `SerrePositivity.InfinityCategories.joinUnion` (SerrePositivity/InfinityCategories/Core/Join.lean:606), `SerrePositivity.InfinityCategories.joinUnion_isPushout` (SerrePositivity/InfinityCategories/Core/JoinLifting.lean:94) |
| [4.3.6.4](https://kerodon.net/tag/018J) | own | own | 二単射を像の部分複体として表す。joinUnion への包含について、左脚が右アノダイン、右脚が左アノダインのいずれからも内アノダイン性を得る。 `SerrePositivity.InfinityCategories.joinUnion_innerAnodyne_of_rightAnodyne` (SerrePositivity/InfinityCategories/Core/JoinAnodyne.lean:24), `SerrePositivity.InfinityCategories.joinUnion_innerAnodyne_of_leftAnodyne` (SerrePositivity/InfinityCategories/Core/JoinAnodyne.lean:41) |
| [4.3.6.8](https://kerodon.net/tag/01BZ) | own | own | q の内ファイブレーション性と K₀ の部分複体を共通の仮定とし、relativeSliceOverMap と relativeCosliceMap に対してそれぞれ右・左ファイブレーション性を与える。 `SerrePositivity.InfinityCategories.relativeSliceOverMap_rightFibration` (SerrePositivity/InfinityCategories/Derived/RelativeSliceRightFibration.lean:14), `SerrePositivity.InfinityCategories.relativeCosliceMap_leftFibration` (SerrePositivity/InfinityCategories/Core/RelativeCoslice.lean:122) |
| [4.4.2.6](https://kerodon.net/tag/019F) | own | own | 準圏の辺について可逆性と全ての始端ホーン充填、可逆性と全ての終端ホーン充填をそれぞれ同値にする。n≥2 の両方向がそろう。 `SerrePositivity.InfinityCategories.isInvertibleEdge_iff_hasFinalHornFillers` (SerrePositivity/InfinityCategories/Core/OuterHornConverse.lean:197), `SerrePositivity.InfinityCategories.hasFinalHornFillers_of_isInvertibleEdge` (SerrePositivity/InfinityCategories/Core/InvertibleEdgeLifting.lean:481), `SerrePositivity.InfinityCategories.IsInvertibleEdge` (SerrePositivity/InfinityCategories/Core/InvertibleEdgeLifting.lean:28), `SerrePositivity.InfinityCategories.isInvertibleEdge_iff_hasInitialHornFillers` (SerrePositivity/InfinityCategories/Core/OuterHornDuality.lean:220) |
| [4.4.3.20](https://kerodon.net/tag/01H6) | own | own | 基底射が内ファイブレーションという、原文の isofibration より弱い仮定で core と引戻しが交換する。同じ頂点からの底変換を取ると原文の標準写像の同型になる。 `SerrePositivity.InfinityCategories.quasicategoryCoreMap_isPullback_of_isPullback` (SerrePositivity/InfinityCategories/F1/Categories/CorePullbackRestriction.lean:21), `SerrePositivity.InfinityCategories.F2.corePullbackIso` (SerrePositivity/InfinityCategories/F1/CatInfinity/CorePullbackIso.lean:69) |
| [4.5.1.10](https://kerodon.net/tag/01DY) | own | own | 二つの準圏の間で、指定 F に対し逆関手と両合成の FunctorIso の存在を要求する。原文の hQCat での逆射と、準圏の同値の述語に対応する。 `SerrePositivity.InfinityCategories.QCatEquivalence` (SerrePositivity/InfinityCategories/Core/Equivalence.lean:56), `SerrePositivity.InfinityCategories.IsQCatEquivalence` (SerrePositivity/InfinityCategories/Core/Equivalence.lean:70) |
| [4.5.4.9](https://kerodon.net/tag/033Z) | own | own | 定義域 K に準圏性を課さない前合成同値の比較がある。関手の同型を与える可逆な各頂点成分を使い、同じ f と f′ の圏論的同値性を両向きに移す。 `SerrePositivity.InfinityCategories.isPrecompositionEquivalence_iff_of_homotopy` (SerrePositivity/InfinityCategories/Core/PrecompositionHomotopy.lean:38), `SerrePositivity.InfinityCategories.IsQCatEquivalence.ofFunctorIso` (SerrePositivity/InfinityCategories/Core/EquivalenceCalculus.lean:24) |
| [4.5.4.12](https://kerodon.net/tag/01EH) | own | own | 二準圏と自明 Kan ファイブレーションを仮定し、同じ射の圏同値性を得る。 `SerrePositivity.InfinityCategories.isQCatEquivalence_of_trivialKanFibration` (SerrePositivity/InfinityCategories/Core/TrivialFibrationEquivalence.lean:87), `SerrePositivity.InfinityCategories.qCatEquivalenceOfTrivialKanFibration` (SerrePositivity/InfinityCategories/Core/TrivialFibrationEquivalence.lean:59) |
| [4.6.2.10](https://kerodon.net/tag/01HX) | own | own | 同じ fat join から join への比較が全 A,B で前合成同値になる。Δ¹ の場合の仮定まで外して原文の結論を得る。 `SerrePositivity.InfinityCategories.isPrecompositionEquivalence_fatJoinComparison` (SerrePositivity/InfinityCategories/Core/FatJoinGeneralComparison.lean:41), `SerrePositivity.InfinityCategories.isPrecompositionEquivalence_fatJoinComparison_of_pushout_left` (SerrePositivity/InfinityCategories/Core/FatJoinComparisonGluing.lean:26) |
| [4.6.4.3](https://kerodon.net/tag/01KH) | own | own | 三つの準圏と二脚 p,q に対し、端点評価を用いる向き付き引戻し laxPullback p q が準圏になる。 `SerrePositivity.InfinityCategories.F2.laxPullback_quasicategory` (SerrePositivity/InfinityCategories/F2/CatInfinity/LaxPullback.lean:31) |
| [4.6.5.1](https://kerodon.net/tag/01KX) | own | own | 単体集合と二頂点だけを仮定する。pinchedHomLeft と pinchedHom はそれぞれ coslice、slice の指定頂点ファイバーに対応する。 `SerrePositivity.InfinityCategories.pinchedHom` (SerrePositivity/InfinityCategories/PinchedHom/Basic.lean:112), `SerrePositivity.InfinityCategories.pinchedHomLeft` (SerrePositivity/InfinityCategories/Core/MappingSpaceLeft.lean:172) |
| [4.6.6.8](https://kerodon.net/tag/04J5) | own | own | 準圏と任意図式 p に対し、sliceConeFamilyMap が slice から p 上の左錐関手のファイバーへの圏同値を与える。 `SerrePositivity.InfinityCategories.isQCatEquivalence_sliceConeFamilyMap` (SerrePositivity/InfinityCategories/Core/SliceConeFamilyEquivalence.lean:50), `SerrePositivity.InfinityCategories.coneFamily` (SerrePositivity/InfinityCategories/Core/ConeFamily.lean:46), `SerrePositivity.InfinityCategories.isQCatEquivalence_cosliceCoconeFamilyMap` (SerrePositivity/InfinityCategories/Core/CosliceCoconeFamilyEquivalence.lean:56) |
| [4.7.3.10](https://kerodon.net/tag/02MY) | own | own | 同値が初期・終頂点を運ぶ。QCatEquivalence の同じ型を逆同値にも適用できるので存在の両向きが対応する。 `SerrePositivity.InfinityCategories.QCatEquivalence.map_isTerminalVertex` (SerrePositivity/InfinityCategories/Core/EquivalenceTerminal.lean:25), `SerrePositivity.InfinityCategories.QCatEquivalence.map_isInitialVertex` (SerrePositivity/InfinityCategories/Core/InitialEquivalence.lean:20) |
| [4.7.3.14](https://kerodon.net/tag/02HM) | own | own | 初期頂点と終頂点の各存在を仮定し、それらが張る全部分複体の Kan 可縮性をそれぞれ結論する。原文の準圏の仮定より弱い。 `SerrePositivity.InfinityCategories.terminalVertices_isContractibleKan` (SerrePositivity/InfinityCategories/Core/TerminalVertices.lean:77), `SerrePositivity.InfinityCategories.terminalVertices` (SerrePositivity/InfinityCategories/Core/TerminalVertices.lean:61), `SerrePositivity.InfinityCategories.F2.Presentable.Duality.initialVertices_isContractibleKan` (SerrePositivity/InfinityCategories/F2/Presentable/Duality/RightUnitContractible.lean:25) |
| [4.9.1.6](https://kerodon.net/tag/03Q0) | mathlib | mathlib | 順序の厳密部分を IsWellOrder に渡す。線形順序で整列性を整礎性により記述し、原文の非空部分集合に最小元がある条件に対応する。 `IsWellOrder` (Mathlib/Order/RelClasses.lean:316) |
| [4.9.1.22](https://kerodon.net/tag/03QG) | mathlib | mathlib | Ordinal.enum の逆向きが順序型未満への順序同型。Ordinal.typein は各元をその下の初期部分の順序型に送り、順序型への列挙との逆関係を Ordinal.enum_typein が与える。整列集合の関係同型の一意性も Ordinal.relIso_enum で確認した。 `Ordinal.enum` (Mathlib/SetTheory/Ordinal/Basic.lean:405), `Ordinal.typein` (Mathlib/SetTheory/Ordinal/Basic.lean:337) |

## none

### [4.4.1.9](https://kerodon.net/tag/056Z) · `none → none`

nerveAdjunction は同じ自然な単位を与える。準圏 C でこの単位自体が内ファイブレーションかつ同値を持ち上げる宣言は確認できない。

- (a) `4.4.1.9` と `4.4.1`、`Kerodon`。直接 0 件、同小節 1 件。参照例 `SerrePositivity/InfinityCategories/Core/InvertibleEdgeLifting.lean:340`。
- (b) `nerve homotopy category unit isofibration / categorification / equivalence lifting`。双対の語 `categorification category equivalence homotopy isofibration lifting nerve unit`。普通圏の語 `categorification category coherent equivalence homotopy isofibration lifting nerve unit`。確認した候補 `nerveAdjunction` (`Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean:389`), `EquivalenceLifting` (`SerrePositivity/InfinityCategories/F1B/Fibrations/EquivalenceLifting.lean:26`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/F1B/Diagrams`, `SerrePositivity/InfinityCategories/F1B/Fibrations` を検索。対象の宣言見出し 414 件。

### [4.5.2.13](https://kerodon.net/tag/03TC) · `none → none`

同型から圏同値を作る定理と自明 Kan から圏同値を作る定理はある。最小な二つの準圏で圏同値から厳密な同型に戻す型は未確認。

- (a) `4.5.2.13` と `4.5.2`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `minimal quasicategory equivalence simplicial isomorphism / minimal Kan / homotopy equivalence`。双対の語 `equivalence homotopy isomorphism kan minimal quasicategory simplicial`。普通圏の語 `equivalence homotopy isomorphism kan minimal quasicategory simplicial`。確認した候補 `isQCatEquivalence_of_trivialKanFibration` (`SerrePositivity/InfinityCategories/Core/TrivialFibrationEquivalence.lean:87`), `qCatEquivalenceOfIso` (`SerrePositivity/InfinityCategories/Core/PrecompositionTensor.lean:24`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory` を検索。対象の宣言見出し 1708 件。

### [4.5.5.8](https://kerodon.net/tag/01FA) · `none → none`

Mathlib の貼り合わせは通常圏の厳密な余極限の比較。任意の単体集合における categorical pushout を貼り合わせる同じ iff は未確認。

- (a) `4.5.5.8` と `4.5.5`、`Kerodon`。直接 0 件、同小節 64 件。参照例 `SerrePositivity/InfinityCategories/Core/EquivalencePathInternalHom.lean:7`, `SerrePositivity/InfinityCategories/Core/EquivalencePathMap.lean:5`。
- (b) `categorical pushout pasting cancellation / homotopy pushout / right square`。双対の語 `cancellation categorical homotopy left pasting pullback square`。普通圏の語 `cancellation categorical homotopy pasting pushout right square`。確認した候補 `pasteHorizIsPushoutEquiv` (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Pasting.lean:331`), `isPrecompositionEquivalence_fatJoinComparison_of_pushout_left` (`SerrePositivity/InfinityCategories/Core/FatJoinComparisonGluing.lean:26`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/Core` を検索。対象の宣言見出し 2340 件。

### [4.5.7.22](https://kerodon.net/tag/034U) · `none → partial`（partial_kind: `special`）

内ファイブレーションを片脚に持つ cospan では core と引戻しの同型がある。任意の isofibrant 図式で core 側の isofibrant 性と全極限比較は未確認。

- (a) `4.5.7.22` と `4.5.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `core isofibrant diagram limit / pointwise maximal Kan subcomplex / core pullback`。双対の語 `colimit core diagram isofibrant kan maximal pointwise pushout subcomplex`。普通圏の語 `core diagram isofibrant kan limit maximal pointwise pullback subcomplex`。確認した候補 `corePullbackIso` (`SerrePositivity/InfinityCategories/F1/CatInfinity/CorePullbackIso.lean:69`), `quasicategoryCoreMap_isPullback_of_isPullback` (`SerrePositivity/InfinityCategories/F1/Categories/CorePullbackRestriction.lean:21`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Limits`, `SerrePositivity/InfinityCategories/HomotopyLimits`, `SerrePositivity/InfinityCategories/Kan`, `SerrePositivity/KST/Spectra` を検索。対象の宣言見出し 13441 件。

### [4.6.8.4](https://kerodon.net/tag/01PK) · `none → none`

両端固定の二点 Hom の写像と、絶対的な三角形空間はある。任意の長さで辺ごとに固定する原文の相対比較の自明 Kan 性は未確認。

- (a) `4.6.8.4` と `4.6.8`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `multi vertex mapping space spine restriction trivial Kan fibration / relative inner fibration`。双対の語 `fibration inner kan mapping multi relative restriction space spine trivial vertex`。普通圏の語 `inner kan lifting mapping multi relative restriction space spine trivial vertex`。確認した候補 `pinchedHomMap_rightFibration` (`SerrePositivity/InfinityCategories/Core/MappingSpaceFibration.lean:197`), `arrowEndpointPair_pinchedHom_fibration` (`SerrePositivity/InfinityCategories/F2/CatInfinity/LaxPullbackMapping.lean:57`), `compositionTriangleSpace_isContractibleKan` (`SerrePositivity/InfinityCategories/F1/Diagrams/CompositionTriangleSpace.lean:63`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/Derived`, `SerrePositivity/InfinityCategories/F1/Coherent`, `SerrePositivity/InfinityCategories/F1/MappingSpaces`, `SerrePositivity/InfinityCategories/Kan` を検索。対象の宣言見出し 10969 件。

### [4.7.1.16](https://kerodon.net/tag/05ET) · `none → none`

終頂点の全境界延長と、空間に限定した 0 切断はある。原文の任意の対象の n 切断性と m≥n+3 での境界充填との iff は未確認。

- (a) `4.7.1.16` と `4.7.1`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `truncated object boundary filling final vertex dimension / terminal vertex extension`。双対の語 `boundary dimension extension filling initial object truncated vertex`。普通圏の語 `boundary dimension extension filling final object terminal truncated vertex`。確認した候補 `IsTerminalVertex` (`SerrePositivity/InfinityCategories/Core/Terminal.lean:80`), `isTerminalVertex_iff_sliceOverExtension` (`SerrePositivity/InfinityCategories/Core/Terminal.lean:89`), `Is0TruncatedSpace` (`SerrePositivity/InfinityCategories/F1/Categories/DiscreteSpace.lean:120`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/Core`, `SerrePositivity/InfinityCategories/F1/Categories`, `SerrePositivity/InfinityCategories/F1B/MappingSpaces` を検索。対象の宣言見出し 2958 件。

### [4.7.4.8](https://kerodon.net/tag/06R3) · `none → partial`（partial_kind: `special`）

射が存在する全頂点の部分圏が C 自身である場合に、終頂点とその slice 射影の自明 Kan 性の比較を確認した。一般の台への制限と subterminal の比較は未確認。

- (a) `4.7.4.8` と `4.7.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `subterminal iff terminal in support / slice projection trivial Kan fibration`。双対の語 `coslice fibration initial kan projection subterminal support trivial`。普通圏の語 `kan lifting projection slice subterminal support terminal trivial`。確認した候補 `isTerminalVertex_iff_trivialKanFibration` (`SerrePositivity/InfinityCategories/Core/Terminal.lean:134`), `IsSubterminal` (`Mathlib/CategoryTheory/Subterminal.lean:43`), `isQCatEquivalence_of_trivialKanFibration` (`SerrePositivity/InfinityCategories/Core/TrivialFibrationEquivalence.lean:87`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory`, `Mathlib/CategoryTheory/Subobject`, `SerrePositivity/InfinityCategories/F1/Categories` を検索。対象の宣言見出し 2499 件。

### [4.7.6.15](https://kerodon.net/tag/06RM) · `none → none`

厳密 Segal 単体集合の 2-coskeletal 性はある。一般の局所 (n−2) 切断性と指定単位の自明 Kan 性の iff は未確認。

- (a) `4.7.6.15` と `4.7.6`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `locally truncated coskeleton unit trivial Kan / strict Segal coskeletal`。双対の語 `kan locally segal skeletal skeleton strict trivial truncated unit`。普通圏の語 `cosk coskeleton kan locally segal strict trivial truncated unit`。確認した候補 `isCoskeletal'` (`Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean:237`), `coskAdj` (`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:146`), `Is0TruncatedSpace` (`SerrePositivity/InfinityCategories/F1/Categories/DiscreteSpace.lean:120`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet` を検索。対象の宣言見出し 1192 件。

### [4.7.6.19](https://kerodon.net/tag/058G) · `none → none`

既存の coskAdj は n-切断単体集合の制限への右随伴。原文の準圏の mapping space の局所 (n−2) 切断の普遍性は未確認。

- (a) `4.7.6.19` と `4.7.6`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `coskeleton local truncation universal property / cosk adjunction / homotopy category`。双対の語 `adjunction category cosk homotopy property skeleton truncation universal`。普通圏の語 `adjunction category cosk coskeleton homotopy property truncation universal`。確認した候補 `coskAdj` (`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:146`), `nerveAdjunction` (`Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean:389`), `Is0TruncatedSpace` (`SerrePositivity/InfinityCategories/F1/Categories/DiscreteSpace.lean:120`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet` を検索。対象の宣言見出し 1192 件。

### [4.7.6.20](https://kerodon.net/tag/058N) · `none → none`

単体集合での切断・coskeleton 随伴はあるが、hQCat の局所 n 切断部分圏への反射とその対象式は未確認。

- (a) `4.7.6.20` と `4.7.6`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `homotopy QCat locally truncated reflective / coskeleton left adjoint / cosk`。双対の語 `adjoint cat cosk homotopy locally reflective right skeleton truncated`。普通圏の語 `adjoint cat cosk coskeleton homotopy left locally reflective truncated`。確認した候補 `coskAdj` (`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:146`), `HomotopyQCat` (`SerrePositivity/InfinityCategories/F1/Categories/HomotopyQCat.lean:33`), `nerveAdjunction` (`Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean:389`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet` を検索。対象の宣言見出し 1192 件。

### [4.7.7.8](https://kerodon.net/tag/057L) · `none → none`

厳密 Segal の 2-coskeletal 性を確認した。任意の n で弱 coskeletal 性と最小性の組を n-category の条件とする iff は未確認。

- (a) `4.7.7.8` と `4.7.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `n category weakly coskeletal minimal dimension n / strict Segal`。双対の語 `category dimension minimal segal skeletal strict weakly`。普通圏の語 `category cosk dimension minimal segal strict weakly`。確認した候補 `isCoskeletal'` (`Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean:237`), `Is0TruncatedSpace` (`SerrePositivity/InfinityCategories/F1/Categories/DiscreteSpace.lean:120`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 1486 件。

### [4.7.7.9](https://kerodon.net/tag/057M) · `none → none`

厳密 coskeleton の性質と離散空間の述語はある。弱 coskeleton と次元での最小性を束ねた n-category の定義は未確認。

- (a) `4.7.7.9` と `4.7.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `n category definition weak coskeleton minimal dimension / quasicategory truncation`。双対の語 `category definition dimension minimal quasicategory skeleton truncation weak`。普通圏の語 `category coskeleton definition dimension minimal quasicategory truncation weak`。確認した候補 `isCoskeletal'` (`Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean:237`), `Is0TruncatedSpace` (`SerrePositivity/InfinityCategories/F1/Categories/DiscreteSpace.lean:120`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 1486 件。

### [4.7.7.24](https://kerodon.net/tag/06RV) · `none → none`

両 slice が準圏になる結論と厳密 Segal の別の性質はある。一般の n-category で両 slice の弱 coskeletal 性と最小性を保つ型は未確認。

- (a) `4.7.7.24` と `4.7.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `n category slice coslice truncated minimal / slice projection quasicategory`。双対の語 `category coslice minimal projection quasicategory slice truncated`。普通圏の語 `category coslice minimal projection quasicategory slice truncated`。確認した候補 `sliceOver_quasicategory` (`SerrePositivity/InfinityCategories/Core/RightFibration.lean:223`), `sliceUnder_quasicategory` (`SerrePositivity/InfinityCategories/Core/RightFibration.lean:330`), `isCoskeletal'` (`Mathlib/AlgebraicTopology/SimplicialSet/Coskeletal.lean:237`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet`, `SerrePositivity/InfinityCategories/F1/Fibrations` を検索。対象の宣言見出し 1486 件。

### [4.7.9.21](https://kerodon.net/tag/06RW) · `none → none`

圏化の随伴と core の引戻し比較はある。下脚がホモトピー n 圏を与える条件で上脚の h≤n が同型となる型は未確認。

- (a) `4.7.9.21` と `4.7.9`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `homotopy n category preserves pullback / truncation functor / categorification`。双対の語 `categorification category functor homotopy preserves pushout truncation`。普通圏の語 `categorification category functor homotopy preserves pullback truncation`。確認した候補 `coskAdj` (`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean:146`), `nerveAdjunction` (`Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean:389`), `corePullbackIso` (`SerrePositivity/InfinityCategories/F1/CatInfinity/CorePullbackIso.lean:69`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/AlgebraicTopology/SimplicialSet` を検索。対象の宣言見出し 1192 件。

### [4.8.2.27](https://kerodon.net/tag/05AP) · `none → partial`（partial_kind: `stronger-hyp`）

元の射が充満忠実な内ファイブレーションである場合、引戻しの射も充満忠実なので n-full の前向きの特殊例に当たる。一般の n-full と全射的な底変換での逆向きは未確認。

- (a) `4.8.2.27` と `4.8.2`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `n full base change categorical pullback / fully faithful pullback / essentially surjective descent`。双対の語 `base categorical change descent essentially faithful full fully pushout surjective`。普通圏の語 `base categorical change descent essentially faithful full fully pullback surjective`。確認した候補 `IsFullyFaithful.pullback_snd` (`SerrePositivity/InfinityCategories/Core/FullyFaithfulBaseChange.lean:106`), `laxPullback_quasicategory` (`SerrePositivity/InfinityCategories/F2/CatInfinity/LaxPullback.lean:31`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory/Functor`, `SerrePositivity/InfinityCategories/Core` を検索。対象の宣言見出し 2616 件。

### [4.8.8.20](https://kerodon.net/tag/06Y6) · `none → none`

相対内部 Hom への制限の内ファイブレーション性を確認した。n-faithful と m−1 connective から同じ制限の n−m-faithful を結論する型は未確認。

- (a) `4.8.8.20` と `4.8.8`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `n faithful m connective relative functor restriction / inner fibration relative hom / precomposition`。双対の語 `connective faithful fibration functor hom inner postcomposition relative restriction`。普通圏の語 `connective faithful functor hom inner lifting precomposition relative restriction`。確認した候補 `kanFiberwiseHomPre_innerFibration` (`SerrePositivity/InfinityCategories/F1B/KanExtension/RelativeHomRestrictionInnerFibration.lean:25`), `IsPrecompositionEquivalence` (`SerrePositivity/InfinityCategories/Core/PrecompositionEquivalence.lean:24`), `IsFullyFaithful` (`SerrePositivity/InfinityCategories/Core/FullyFaithful.lean:24`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/Core` を検索。対象の宣言見出し 2340 件。

### [4.9.4.21](https://kerodon.net/tag/05YP) · `none → none`

各有限単体集合にコードを選べることと一つの単体集合の単体の可算性はある。次元と非退化単体数を固定した同型類の有限性は未確認。

- (a) `4.9.4.21` と `4.9.4`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `finite number of finite simplicial sets fixed cells / finite simplicial code countable / nondegenerate`。双対の語 `cells code countable finite fixed nondegenerate number sets simplicial`。普通圏の語 `cells code countable finite fixed nondegenerate number sets simplicial`。確認した候補 `exists_finiteSimplicialCode` (`SerrePositivity/InfinityCategories/F2/Presentable/FiniteSimplicialCodes.lean:65`), `countable_simplices_of_countable_levels` (`SerrePositivity/InfinityCategories/F2/Presentable/Supply/CountableFiniteExhaustion.lean:26`)。
- (c) 同小節の own・bothを起点に (b) の語で `SerrePositivity/InfinityCategories/Core/FilteredExchange` を検索。対象の宣言見出し 271 件。

### [4.9.6.1](https://kerodon.net/tag/03TK) · `none → none`

小さい Kan 模型の存在と元が小さい場合を確認した。π₀ と全ての正次数ホモトピー群の κ-小ささによる iff は未確認。

- (a) `4.9.6.1` と `4.9.6`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `essentially kappa small Kan iff homotopy groups / pi0 cardinality / small Kan model`。双対の語 `cardinality essentially groups homotopy kan kappa model pi0 small`。普通圏の語 `cardinality essentially groups homotopy kan kappa model pi0 small`。確認した候補 `HasSmallKanModel` (`SerrePositivity/InfinityCategories/F1/Universe/SmallKanModel.lean:22`), `hasSmallKanModel_of_small` (`SerrePositivity/InfinityCategories/F1/Universe/SmallKanModel.lean:33`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `SerrePositivity/InfinityCategories/F1/Universe` を検索。対象の宣言見出し 178 件。

### [4.9.7.8](https://kerodon.net/tag/03UR) · `none → none`

既存の局所小ささは宇宙で表し、単独の準圏の Hom に適用する。κ・λ の指数共終性を仮定した一般の関手圏の λ-小ささは未確認。

- (a) `4.9.7.8` と `4.9.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `local lambda small functor category kappa small shape / exponential cofinality / mapping spaces`。双対の語 `category cofinality exponential functor kappa lambda mapping shape small spaces`。普通圏の語 `category cofinality exponential functor kappa lambda mapping shape small spaces`。確認した候補 `IsLocallySmall` (`SerrePositivity/InfinityCategories/F2/Presentable/LocallySmall.lean:26`), `IsLocallySmall.hom_small` (`SerrePositivity/InfinityCategories/F2/Presentable/LocallySmallHomTypes.lean:26`), `HasSmallKanModel` (`SerrePositivity/InfinityCategories/F1/Universe/SmallKanModel.lean:22`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory`, `SerrePositivity/InfinityCategories/F2/Presentable` を検索。対象の宣言見出し 3941 件。

### [4.9.7.9](https://kerodon.net/tag/03US) · `none → partial`（partial_kind: `special`）

Mathlib の EssentiallySmall.lean のインスタンスは通常の小圏を始域にし、局所小な余域への関手圏を局所小にする。原文の準圏の写像空間を含む一般形は未確認。

- (a) `4.9.7.9` と `4.9.7`、`Kerodon`。直接 0 件、同小節 0 件。
- (b) `essentially small functor category locally small / natural transformation small / ordinary case`。双対の語 `case category essentially functor locally natural ordinary small transformation`。普通圏の語 `case category essentially functor locally natural ordinary small transformation`。確認した候補 `instLocallySmallFunctor` (`Mathlib/CategoryTheory/EssentiallySmall.lean:310`)。
- (c) 同小節の mathlib・partialを起点に (b) の語で `Mathlib/CategoryTheory`, `SerrePositivity/InfinityCategories/F2/Presentable` を検索。対象の宣言見出し 3941 件。

## 照合に使った kernel 型

段1・段1′と対象章の kernel evidence にある型。表示用に空白を整えた。

### 4.2.1.1

```lean
@SerrePositivity.InfinityCategories.LeftFibration.{u_1} : {X Y : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X Y → Prop
@SerrePositivity.InfinityCategories.RightFibration.{u_1} : {X Y : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} X Y → Prop
SerrePositivity.InfinityCategories.leftFibrations.{u_1} : CategoryTheory.MorphismProperty.{u_1, u_1 + 1} SSet.{u_1}
```

### 4.2.5.3

```lean
@SerrePositivity.InfinityCategories.leftAnodyneExtensions_pushoutObjObj_left.{u_1} : ∀ {A D K L : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} D A), SerrePositivity.InfinityCategories.leftAnodyneExtensions.{u_1} i → ∀ (j : Quiver.Hom.{u_1, u_1 + 1} K L) [CategoryTheory.Mono.{u_1, u_1 + 1} j] (sq : CategoryTheory.Functor.PushoutObjObj.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalCategory.curriedTensor.{u_1, u_1 + 1} SSet.{u_1}) i j), SerrePositivity.InfinityCategories.leftAnodyneExtensions.{u_1} (CategoryTheory.Functor.PushoutObjObj.ι.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} sq)
@SerrePositivity.InfinityCategories.leftAnodyneExtensions_pushoutObjObj_right.{u_1} : ∀ {A D K L : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} D A) [CategoryTheory.Mono.{u_1, u_1 + 1} i] (j : Quiver.Hom.{u_1, u_1 + 1} K L), SerrePositivity.InfinityCategories.leftAnodyneExtensions.{u_1} j → ∀ (sq : CategoryTheory.Functor.PushoutObjObj.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalCategory.curriedTensor.{u_1, u_1 + 1} SSet.{u_1}) i j), SerrePositivity.InfinityCategories.leftAnodyneExtensions.{u_1} (CategoryTheory.Functor.PushoutObjObj.ι.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} sq)
@SerrePositivity.InfinityCategories.cofinalRightAnodyne_pushoutObjObj_right.{u_1} : ∀ {A D K L : SSet.{u_1}} (i : Quiver.Hom.{u_1, u_1 + 1} D A) [CategoryTheory.Mono.{u_1, u_1 + 1} i] (j : Quiver.Hom.{u_1, u_1 + 1} K L), SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} j → ∀ (sq : CategoryTheory.Functor.PushoutObjObj.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} (CategoryTheory.MonoidalCategory.curriedTensor.{u_1, u_1 + 1} SSet.{u_1}) i j), SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} (CategoryTheory.Functor.PushoutObjObj.ι.{u_1, u_1, u_1, u_1 + 1, u_1 + 1, u_1 + 1} sq)
```

### 4.3.3.1

```lean
@IsLowerSet.{u_1} : {α : Type u_1} → [LE.{u_1} α] → Set.{u_1} α → Prop
```

### 4.3.6.1

```lean
@SerrePositivity.InfinityCategories.sliceOverProjection_rightFibration.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X), SerrePositivity.InfinityCategories.RightFibration.{u_1} (SerrePositivity.InfinityCategories.sliceOverProjection.{u_1} p)
@SerrePositivity.InfinityCategories.sliceUnderProjection_leftFibration.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X), SerrePositivity.InfinityCategories.LeftFibration.{u_1} (SerrePositivity.InfinityCategories.sliceUnderProjection.{u_1} p)
@SerrePositivity.InfinityCategories.sliceOver_quasicategory.{u_1} : ∀ {K X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X), SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.sliceOver.{u_1} p)
```

### 4.3.6.3

```lean
@SerrePositivity.InfinityCategories.joinUnion.{u_1} : {A B : SSet.{u_1}} → SSet.Subcomplex.{u_1} A → SSet.Subcomplex.{u_1} B → SSet.Subcomplex.{u_1} (SerrePositivity.InfinityCategories.join.{u_1} A B)
@SerrePositivity.InfinityCategories.joinUnion_isPushout.{u_1} : ∀ {A B : SSet.{u_1}} (A₀ : SSet.Subcomplex.{u_1} A) (B₀ : SSet.Subcomplex.{u_1} B), CategoryTheory.IsPushout.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.joinMap.{u_1} (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} A₀)) (SSet.Subcomplex.ι.{u_1} B₀)) (SerrePositivity.InfinityCategories.joinMap.{u_1} (SSet.Subcomplex.ι.{u_1} A₀) (CategoryTheory.CategoryStruct.id.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} B₀))) (SerrePositivity.InfinityCategories.joinUnionLeft.{u_1} A₀ B₀) (SerrePositivity.InfinityCategories.joinUnionRight.{u_1} A₀ B₀)
```

### 4.3.6.4

```lean
@SerrePositivity.InfinityCategories.joinUnion_innerAnodyne_of_rightAnodyne.{u_1} : ∀ {A B : SSet.{u_1}} (A₀ : SSet.Subcomplex.{u_1} A) (B₀ : SSet.Subcomplex.{u_1} B), SerrePositivity.InfinityCategories.rightAnodyneExtensions.{u_1} (SSet.Subcomplex.ι.{u_1} A₀) → SSet.innerAnodyneExtensions.{u_1} (SSet.Subcomplex.ι.{u_1} (SerrePositivity.InfinityCategories.joinUnion.{u_1} A₀ B₀))
@SerrePositivity.InfinityCategories.joinUnion_innerAnodyne_of_leftAnodyne.{u_1} : ∀ {A B : SSet.{u_1}} (A₀ : SSet.Subcomplex.{u_1} A) (B₀ : SSet.Subcomplex.{u_1} B), SerrePositivity.InfinityCategories.leftAnodyneExtensions.{u_1} (SSet.Subcomplex.ι.{u_1} B₀) → SSet.innerAnodyneExtensions.{u_1} (SSet.Subcomplex.ι.{u_1} (SerrePositivity.InfinityCategories.joinUnion.{u_1} A₀ B₀))
```

### 4.3.6.8

```lean
@SerrePositivity.InfinityCategories.relativeSliceOverMap_rightFibration.{u_1} : ∀ {K E B : SSet.{u_1}} (p : Quiver.Hom.{u_1, u_1 + 1} K E) (r : Quiver.Hom.{u_1, u_1 + 1} E B) [SSet.InnerFibration.{u_1} r] (K₀ : SSet.Subcomplex.{u_1} K), SerrePositivity.InfinityCategories.RightFibration.{u_1} (SerrePositivity.InfinityCategories.relativeSliceOverMap.{u_1} p (SSet.Subcomplex.ι.{u_1} K₀) r)
@SerrePositivity.InfinityCategories.relativeCosliceMap_leftFibration.{u_1} : ∀ {K X Y : SSet.{u_1}} (p : Quiver.Hom.{u_1, u_1 + 1} K X) (q : Quiver.Hom.{u_1, u_1 + 1} X Y) [SSet.InnerFibration.{u_1} q] (K₀ : SSet.Subcomplex.{u_1} K), SerrePositivity.InfinityCategories.LeftFibration.{u_1} (SerrePositivity.InfinityCategories.relativeCosliceMap.{u_1} p q K₀)
```

### 4.4.2.6

```lean
@SerrePositivity.InfinityCategories.isInvertibleEdge_iff_hasFinalHornFillers.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} (e : SSet.Truncated.Edge.{u_1} x y), SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} e ↔ SerrePositivity.InfinityCategories.HasFinalHornFillers.{u_1} e
@SerrePositivity.InfinityCategories.hasFinalHornFillers_of_isInvertibleEdge.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} (e : SSet.Truncated.Edge.{u_1} x y), SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} e → SerrePositivity.InfinityCategories.HasFinalHornFillers.{u_1} e
@SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} : {X : SSet.{u_1}} → {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} → SSet.Truncated.Edge.{u_1} x y → Prop
@SerrePositivity.InfinityCategories.isInvertibleEdge_iff_hasInitialHornFillers.{u_1} : ∀ {X : SSet.{u_1}} [SSet.Quasicategory.{u_1} X] {x y : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })} (e : SSet.Truncated.Edge.{u_1} x y), SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} e ↔ SerrePositivity.InfinityCategories.HasInitialHornFillers.{u_1} e
```

### 4.4.3.20

```lean
@SerrePositivity.InfinityCategories.quasicategoryCoreMap_isPullback_of_isPullback.{u_1} : ∀ {A B C D : SSet.{u_1}} [SSet.Quasicategory.{u_1} B] [SSet.Quasicategory.{u_1} C] [SSet.Quasicategory.{u_1} D] {p : Quiver.Hom.{u_1, u_1 + 1} A B} {q : Quiver.Hom.{u_1, u_1 + 1} A C} {f : Quiver.Hom.{u_1, u_1 + 1} B D} {g : Quiver.Hom.{u_1, u_1 + 1} C D} [SSet.InnerFibration.{u_1} f], CategoryTheory.IsPullback.{u_1, u_1 + 1} p q f g → CategoryTheory.IsPullback.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} p) (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} q) (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} f) (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} g)
@SerrePositivity.InfinityCategories.F2.corePullbackIso.{u_1} : {E F B : SSet.{u_1}} → [SSet.Quasicategory.{u_1} E] → [SSet.Quasicategory.{u_1} F] → [SSet.Quasicategory.{u_1} B] → (p : Quiver.Hom.{u_1, u_1 + 1} E B) → (q : Quiver.Hom.{u_1, u_1 + 1} F B) → [SSet.InnerFibration.{u_1} p] → CategoryTheory.Iso.{u_1, u_1 + 1} (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.quasicategoryCore.{u_1} (CategoryTheory.Limits.pullback.{u_1, u_1 + 1} p q))) (CategoryTheory.Limits.pullback.{u_1, u_1 + 1} (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} p) (SerrePositivity.InfinityCategories.quasicategoryCoreMap.{u_1} q))
```

### 4.5.1.10

```lean
SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} : (X Y : SSet.{u_1}) → [SSet.Quasicategory.{u_1} X] → [SSet.Quasicategory.{u_1} Y] → Type u_1
@SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} : {X Y : SSet.{u_1}} → [SSet.Quasicategory.{u_1} X] → [SSet.Quasicategory.{u_1} Y] → Quiver.Hom.{u_1, u_1 + 1} X Y → Prop
```

### 4.5.4.9

```lean
@SerrePositivity.InfinityCategories.isPrecompositionEquivalence_iff_of_homotopy.{u_1} : ∀ {A B : SSet.{u_1}} {f g : Quiver.Hom.{u_1, u_1 + 1} A B} (H : SSet.Homotopy.{u_1} f g), (∀ (a : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} A (Opposite.op.{1} { len := 0 })), SerrePositivity.InfinityCategories.IsInvertibleEdge.{u_1} (SSet.Edge.toTruncated.{u_1} (SerrePositivity.InfinityCategories.simplicialHomotopyVertexEdge.{u_1} H a))) → (SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} f ↔ SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} g)
@SerrePositivity.InfinityCategories.IsQCatEquivalence.ofFunctorIso.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] {f g : Quiver.Hom.{u_1, u_1 + 1} X Y}, SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} f → ∀ (e : SerrePositivity.InfinityCategories.FunctorIso.{u_1} f g), SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} g
```

### 4.5.4.12

```lean
@SerrePositivity.InfinityCategories.isQCatEquivalence_of_trivialKanFibration.{u_1} : ∀ {E B : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} E] [inst_1 : SSet.Quasicategory.{u_1} B] (p : Quiver.Hom.{u_1, u_1 + 1} E B) [SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1} p], SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} p
@SerrePositivity.InfinityCategories.qCatEquivalenceOfTrivialKanFibration.{u_1} : {E B : SSet.{u_1}} → [inst : SSet.Quasicategory.{u_1} E] → [inst_1 : SSet.Quasicategory.{u_1} B] → (p : Quiver.Hom.{u_1, u_1 + 1} E B) → [SerrePositivity.InfinityCategories.TrivialKanFibration.{u_1} p] → SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} E B
```

### 4.6.2.10

```lean
SerrePositivity.InfinityCategories.isPrecompositionEquivalence_fatJoinComparison.{u_1} : ∀ (A B : SSet.{u_1}), SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} A B)
@SerrePositivity.InfinityCategories.isPrecompositionEquivalence_fatJoinComparison_of_pushout_left.{u_1} : ∀ {A B C D : SSet.{u_1}} {f : Quiver.Hom.{u_1, u_1 + 1} A B} [CategoryTheory.Mono.{u_1, u_1 + 1} f] {g : Quiver.Hom.{u_1, u_1 + 1} A C} {r : Quiver.Hom.{u_1, u_1 + 1} B D} {t : Quiver.Hom.{u_1, u_1 + 1} C D}, CategoryTheory.IsPushout.{u_1, u_1 + 1} f g r t → ∀ (K : SSet.{u_1}), SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} A K) → SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} B K) → SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} C K) → SerrePositivity.InfinityCategories.IsPrecompositionEquivalence.{u_1} (SerrePositivity.InfinityCategories.fatJoinComparison.{u_1} D K)
```

### 4.6.4.3

```lean
@SerrePositivity.InfinityCategories.F2.laxPullback_quasicategory.{u_1} : ∀ {A B C : SSet.{u_1}} [SSet.Quasicategory.{u_1} A] [SSet.Quasicategory.{u_1} B] [SSet.Quasicategory.{u_1} C] (p : Quiver.Hom.{u_1, u_1 + 1} A C) (q : Quiver.Hom.{u_1, u_1 + 1} B C), SSet.Quasicategory.{u_1} (SerrePositivity.InfinityCategories.F2.laxPullback.{u_1} p q)
```

### 4.6.5.1

```lean
@SerrePositivity.InfinityCategories.pinchedHom.{u_1} : {X : SSet.{u_1}} → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → SSet.{u_1}
@SerrePositivity.InfinityCategories.pinchedHomLeft.{u_1} : {X : SSet.{u_1}} → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 }) → SSet.{u_1}
```

### 4.6.6.8

```lean
@SerrePositivity.InfinityCategories.isQCatEquivalence_sliceConeFamilyMap.{u_1} : ∀ {K X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X), SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} (SerrePositivity.InfinityCategories.sliceConeFamilyMap.{u_1} p)
@SerrePositivity.InfinityCategories.coneFamily.{u_1} : {J X : SSet.{u_1}} → Quiver.Hom.{u_1, u_1 + 1} J X → SSet.{u_1}
@SerrePositivity.InfinityCategories.isQCatEquivalence_cosliceCoconeFamilyMap.{u_1} : ∀ {K X : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] (p : Quiver.Hom.{u_1, u_1 + 1} K X), SerrePositivity.InfinityCategories.IsQCatEquivalence.{u_1} (SerrePositivity.InfinityCategories.cosliceCoconeFamilyMap.{u_1} p)
```

### 4.7.3.10

```lean
@SerrePositivity.InfinityCategories.QCatEquivalence.map_isTerminalVertex.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] (e : SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} X Y) {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}, SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} x → SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.QCatEquivalence.hom.{u_1} e) (Opposite.op.{1} { len := 0 }))) x)
@SerrePositivity.InfinityCategories.QCatEquivalence.map_isInitialVertex.{u_1} : ∀ {X Y : SSet.{u_1}} [inst : SSet.Quasicategory.{u_1} X] [inst_1 : SSet.Quasicategory.{u_1} Y] (e : SerrePositivity.InfinityCategories.QCatEquivalence.{u_1} X Y) {x : CategoryTheory.Functor.obj.{0, u_1, 0, u_1 + 1} X (Opposite.op.{1} { len := 0 })}, SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x → SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} ((CategoryTheory.ConcreteCategory.hom.{u_1, u_1, u_1 + 1, u_1} (CategoryTheory.NatTrans.app.{0, u_1, 0, u_1 + 1} (SerrePositivity.InfinityCategories.QCatEquivalence.hom.{u_1} e) (Opposite.op.{1} { len := 0 }))) x)
```

### 4.7.3.14

```lean
@SerrePositivity.InfinityCategories.terminalVertices_isContractibleKan.{u_1} : ∀ {X : SSet.{u_1}}, (∃ x, SerrePositivity.InfinityCategories.IsTerminalVertex.{u_1} x) → SerrePositivity.InfinityCategories.IsContractibleKan.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.terminalVertices.{u_1} X))
SerrePositivity.InfinityCategories.terminalVertices.{u_1} : (X : SSet.{u_1}) → SSet.Subcomplex.{u_1} X
@SerrePositivity.InfinityCategories.F2.Presentable.Duality.initialVertices_isContractibleKan.{u_1} : ∀ {X : SSet.{u_1}}, (∃ x, SerrePositivity.InfinityCategories.IsInitialVertex.{u_1} x) → SerrePositivity.InfinityCategories.IsContractibleKan.{u_1} (SSet.Subcomplex.toSSet.{u_1} (SerrePositivity.InfinityCategories.fullSubcomplexOnVertices.{u_1} X SerrePositivity.InfinityCategories.IsInitialVertex.{u_1}))
```

### 4.9.1.6

```lean
IsWellOrder.{u_1} : (α : Type u_1) → (α → α → Prop) → Prop
```

### 4.9.1.22

```lean
@Ordinal.enum.{u_1} : {α : Type u_1} → (r : α → α → Prop) → [inst : IsWellOrder.{u_1} α r] → @RelIso.{u_1 + 1, u_1} (@Set.Elem.{u_1 + 1} Ordinal.{u_1} (@Set.Iio.{u_1 + 1} Ordinal.{u_1} (@PartialOrder.toPreorder.{u_1 + 1} Ordinal.{u_1} Ordinal.partialOrder.{u_1}) (@Ordinal.type.{u_1} α r inst))) α (fun x1 x2 => @LT.lt.{u_1 + 1} (@Set.Elem.{u_1 + 1} Ordinal.{u_1} (@Set.Iio.{u_1 + 1} Ordinal.{u_1} (@PartialOrder.toPreorder.{u_1 + 1} Ordinal.{u_1} Ordinal.partialOrder.{u_1}) (@Ordinal.type.{u_1} α r inst))) (@Subtype.instLT.{u_1 + 1} Ordinal.{u_1} (@Preorder.toLT.{u_1 + 1} Ordinal.{u_1} (@PartialOrder.toPreorder.{u_1 + 1} Ordinal.{u_1} Ordinal.partialOrder.{u_1})) fun x => @Membership.mem.{u_1 + 1, u_1 + 1} Ordinal.{u_1} (Set.{u_1 + 1} Ordinal.{u_1}) (@Set.instMembership.{u_1 + 1} Ordinal.{u_1}) (@Set.Iio.{u_1 + 1} Ordinal.{u_1} (@PartialOrder.toPreorder.{u_1 + 1} Ordinal.{u_1} Ordinal.partialOrder.{u_1}) (@Ordinal.type.{u_1} α r inst)) x) x1 x2) r
@Ordinal.typein.{u_1} : {α : Type u_1} → (r : α → α → Prop) → [IsWellOrder.{u_1} α r] → @PrincipalSeg.{u_1, u_1 + 1} α Ordinal.{u_1} r fun x1 x2 => @LT.lt.{u_1 + 1} Ordinal.{u_1} (@Preorder.toLT.{u_1 + 1} Ordinal.{u_1} (@PartialOrder.toPreorder.{u_1 + 1} Ordinal.{u_1} Ordinal.partialOrder.{u_1})) x1 x2
```
