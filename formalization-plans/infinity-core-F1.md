# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-20）

### 現在地

- F1a〜F1c の fibration・transport・coherent nerve の基盤を提供済み。F1d は未完了。
- left fibrations と strict transport の像の coherent nerve の同値、strict Kan 図式と有限鎖の nerve 上の coherent 図式の復元は関手同型まで構成済み。
- weighted nerve の豊穣な標準単位は各成分で単射かつ同値。単位に沿う strict な比較の制限は
  trivial Kan fibration、延長空間は可縮。strict transport の像で同値な厳密な左逆も存在する。
- 底と図式の共同実現で、`kanDiagramRealization C` と `weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C` の大域的な関手同型を構成済み。
- 表現を `LeftTransportRepresentation` に束ねた。任意の底変換は底側と全空間側の両射を厳密に保ち、
  両射の一致は表現の一致と同値。通常の nerve 上の小さい left fibration の実際の表現も構成済み。
- 射影の各次数の fiber が小さい場合、任意の底・パラメーターで単射に沿う境界固定延長と延長空間の可縮性を証明済み。任意の cartesian な全空間表示への厳密な延長にも適用済み。
- 可換四角形全体を関手空間の引き戻し `transportSquareSpace p` として構成。
  分類図式への射影は left fibration、固定図式上の fiber は相対関手空間と同型。
  表現を表す頂点の全部分複体 `transportWitnessSpace p` は Kan 複体。
  実際の表現との頂点全単射、任意の底変換への制限、頂点での厳密な制限の回収を証明済み。
- 単射への表現空間の制限は Kan fibration、inner anodyne なら trivial Kan fibration
  （Lemma 5.6.8.10 の空間値版）。指定表現の厳密な延長と、その延長空間の可縮性を証明済み。
  全頂点を被覆する制限は表現条件を反映する。小さい次数 fiber の一般の底上の表現空間は可縮。
- left fibration に沿う inner anodyne 射の逆像は前合成同値（Lemma 5.3.6.6 の空間値版）。
  replacement のホーン逆像の pushout 分解、任意の底変換後の scaffold 比較、依存積の随伴で証明。
- `parametrizedFiberTransport` は固定端点の写像空間全体で選択独立性・パラメーター制限・係数変更を保ち、各辺で既存の transport を回収する。
  unstraightening の写像空間比較の fiber 作用と、対象評価後の普遍輸送を関手同型で結んだ。
- 実際の pointed-space 射影の普遍輸送は写像空間上で同値。豊穣合成・反転・底の同型で証明済み。
  始点同値に制限した同時端点制限、両端同値の円柱四角形の端点制限は trivial Kan fibration。
  元の区間の境界上の全空間を両端 fiber の直和と同定。指定境界表現から実際の両端同値を回収した。
  境界固定 lift 族、四角形の二条件同時 fiber、実際の境界制限の fiber を厳密な同型で結んだ。
  全頂点を被覆する制限では、表現空間の fiber と周囲の四角形の fiber は厳密に同型。
  実際の区間上の表現空間の境界制限は trivial Kan fibration（Lemma 5.6.9.1 の空間値版）。
  積上の表現空間と内部 Hom の同型は実際の底変換制限に自然。底の同型でも表現空間は厳密に同型。
  任意の底・小さい次数 fiber の分類図式と比較を構成。指定した単位変換の実際の射は余単位の逆であり、両者の底変換の自然性と普遍比較の実際の成分との一致を証明済み。族の制限の自然性と余単位の整合性も全高次パラメーターで証明済み。
  任意の相対射の collage は区間と底の積上の left fibration。一般の二表現の相対射の族の復元と一意性、相対関手空間全体から分類図式の変換空間への実際の比較射を構成済み。底が ∞ 圏の場合、一般の比較射の同値性を実際の前後合成との可換同型から証明済み。任意の底で、恒等射の族を恒等変換の族へ送る関手同型と、恒等変換のパラメーター制限の厳密な可換性も証明済み。全高次パラメーターで合成三角形を構成し、実際の相対豊穣合成の像を長辺と関手同型で比較した。指定三角形を保った同じ比較も証明済み。任意の inner anodyne な面で、空間値図式と pointed 比較を共同で延長し、部分パラメーター上の既存の両図式を厳密に保つ定理も証明済み。固定図式の面の lift 射影は trivial Kan fibration、各 fiber は可縮。標準表現上では元の unstraightening 比較射が明示的な逆。元の unstraightening の写像空間比較の同値性は任意の底で証明済み（区間・pinched 模型、小さい場合は宇宙縮小後とも）。
- 全 left fibrations 上で切断の頂点評価・部分図式への制限を豊穣比較から coherent な辺に実現。left anodyne な始点評価・制限は大域的な関手同型。
  底の一本の辺に沿う全対象の実際の transport の辺・prism と厳密な両端、切断の始点・終点評価による特徴づけを構成済み。
- 任意の小圏で添字付けた豊穣比較の図式を KanEnrichedDiagram として coherent に実現。任意の添字関手の制限（面・退化を含む）と厳密に可換。合成三点図式の三面は既存の比較の族と厳密に一致。既存の比較の辺そのものの合成三角形と合成等式を証明済み。全対象の transport も底の三角形の合成則・既存三辺の二単体・退化辺の単位則を証明済み。任意の豊穣図式を一本の射へ制限した族は、既存の比較の族と全高次で厳密に一致する。実現の辺そのものの一致と、共同切断評価への特殊化も証明済み。共同降下で選んだ同型の単体圏の任意の辺に対する自然性も証明済み。一単体から終点への制限の辺は初頂点写像で元の辺へ、始点への制限の辺は始点の退化辺へ写る。底上の可換三角形の制限と fiber 評価の合成則を、評価点の等式による輸送を含めて証明済み。任意の単体作用素と評価点で共同切断の制限と fiber 評価は可換で、同じ降下同型の自然性にも合成済み。初頂点の fiber 比較の射は、同じ降下同型の成分・端点の等式・実際の切断評価の合成として明示済み。
- 全単体の共同切断評価と、底に自然な初頂点写像 λ を構成済み。λ は任意の底で、同じ宇宙および任意の宇宙へ持ち上げた quasicategory 標的への局所化。単体圏の nerve は全ての小余極限と単射を保ち、反転関手は実際の極限表示を持つ。単射上の反転関手の制限の inner fibration、相対可逆 path と同時解像の両端の trivial Kan fibration、可算の塔の比較を使って、単射 pushout と可算骨格で証明済み。共同降下で任意の底の leftStraighteningInfinityMap を構成し、初頂点制限と各頂点の fiber 評価への大域的な関手同型を構成済み。実際の辺は両端の指定 evaluateIso による既存 transport の共役とホモトピー圏で一致する。Kan 値豊穣図式の比較・豊穣関手での前合成・共同対角評価・比較の二点図式・実際の共同族を構成済み。単体の共同切断と under の切断は全対象・全添字・全高次で一つの関手同型を持つ。相対関手空間の底変換同型は前合成・高次の後合成と自然で、同じ共同実現により under の切断と初頂点写像の引き戻しの strict transport を同定済み。leftStraighteningInfinityMap_firstVertexRestrictionIso は、一般の射の初頂点制限を leftFibrationInfinityBaseChange λ ≫ leftStraighteningCoherentMap に接続する。任意の小さい底で、実際の対象図式と任意の相対表現の図式の関手同型を、通常の nerve 上の表現と局所化の充満忠実性から構成済み。小さい unstraightening への余単位成分と実際の分類写像の本質的全射性も証明済み。底が ∞ 圏なら、実際の図式からの底上の復元射・その前合成同値性・left fibrations の coherent nerve 内の単位同型成分も構成済み。任意の底変換について、共同切断の豊穣比較を初頂点局所化で降下し、実際の分類写像と引き戻しを全対象・全高次で比較済み。一点上では実際の分類写像を順方向とする分類同値も証明済み。底が ∞ 圏なら、実際の復元射から元の写像空間と実際の対象図式の変換空間の比較同値を構成済み。Hom 自体の edgewise 解像へ任意の豊穣関手・比較・添字付き図式を移す構成と、係数の左右の射影の共同実現を構成済み。直値と反転係数の strict transport の全対象の関手同型を得た。反転側は各 fibration で既存の leftCoherentTransport の図式全体を厳密に回収する。任意の底の初頂点制限も、この同じ反転 transport の族へ全高次で接続済み。対象ごとの相対表現との主比較は、この同じ共同関手同型の成分を使う。表現の全空間側の共同比較と分類写像自体の pinchedHomMap との全高次の照合は未証明。相対表現との比較の全対象の自然性・一般の底の充満忠実性・三角恒等式は残る。
  共同切断評価と λ は同じ指定辺を反転する。局所化の降下は対象ごとの選択ではなく、反転関手全体の coherent な逆と大域的な関手同型として構成済み。
- 対象ビルド3327 jobs、公理監査7818宣言が成功。依存公理は標準3公理のみ。ルート全体は検査対象外。

### 残り（依存順）

見積もりは再開後の実作業時間の粗い幅で、研究上の障害による上振れがある。

1. 次数 fiber の小ささを essentially small な ∞ 圏的 fiber のみの条件へ弱め、相対表現の延長へ一般化する。
   Kerodon Theorem 5.6.5.12、Corollary 5.6.5.15。40〜160時間。
2. 実際の対象図式と相対表現の比較・単位と余単位の成分を全対象の coherent な自然性へ拡張し、充満忠実性と随伴の三角恒等式を完成する。本質的全射性は任意の小さい底で証明済み。
   Kerodon Corollary 5.6.0.6、§5.6.5。24〜100時間。
3. 必要な宇宙の一般化と cocartesian・Cat_∞ 値の分類へ進む。
   Kerodon Theorem 5.6.0.2、§5.5。80〜240時間以上。
4. F1h：twisted arrow、Hom 関手、前層、Yoneda の充満忠実性。
   Kerodon §§8.1〜8.3。40〜160時間。Kan 拡張は α2b の成果を使用可能。
5. F1i：通常の圏の nerve 上で Grothendieck 構成と Yoneda を回収する。
   Kerodon §§5.6、8.3 の通常圏への特殊化。8〜32時間。

### 主要宣言（名前のみ）

- `IsCartesianEdge`、`IsCocartesianEdge`、`SpaceInfinity`、`CatInfinity`
- `leftStraighteningCoherentMap`、`smallLeftUnstraighteningObject`
- `leftStrictTransportInfinityEquivalence`、`leftUnstraighteningMappingSpaceMap`
- `weightedNerveStraighteningCoherentUnitIso`、`weightedNerveStraighteningCoherentFamilyUnitIso`
- `LeftTransportRepresentation`、`LeftTransportRepresentation.restrict`
- `transportWitnessSpace`、`transportWitnessVertexEquiv`、`transportWitnessSpace_kanComplex`
- `leftFibration_pullback_innerAnodyne_isPrecompositionEquivalence`
- `HasSmallSimplexFibers`、`smallFiberTransportWitnessSpace_isContractibleKan`、`smallFiberTransportWitnessRestriction_trivialKanFibration`
- `exists_small_leftTransportRepresentation_extension`、`exists_small_transportWitnessFamily_lift`
- `FiberTransportFamily`、`parametrizedFiberTransport`
- `leftUnstraighteningMappingFiberHom_parametrizedIso`
- `coherentStraighteningCounit`、`coherentStraighteningUnitTransformation_eq_counit_inv`、`transportRepresentationMappingSpaceMap`、`smallFiberLeftStraighteningMappingSpaceMap`、`transportRepresentationUnstraighteningMappingEquivalence`、`kanEnrichedComparisonEdge_compStruct`、`leftFibrationNaturalTransportCompStruct`、`transportSimplexSectionInfinity`、`relativeSectionFirstVertexRestrictionIso`、`transportSimplexFirstVertexMap`、`transportSimplexInitialEdgesLifted`、`transportStandardFirstVertexSection_comp`、`ordinaryComparisonHomotopy`、`transportStandardInvertingDescentIso`、`transportStandardInvertingFamilyIso`、`transportSimplexFirstVertexMap_standard_isLocalization`、`transportSimplexSubcomplexIso`、`transportSimplexNerve_bicart_isPushout`、`transportSimplexLocalizationComparison`、`transportSimplexInvertsEdges_of_isPushout`、`transportSimplexInverting_bicart_isPullback`、`transportSimplexChainEquiv`、`transportSimplexNerve_isPushout`、`transportSimplexInverting_isPullback_of_isPushout`、`transportSimplexInvertingRestriction_innerFibration`、`FunctorIso.invertsEdges_iff`、`fullSubcomplexEquivalencePathLift_map`、`transportSimplexInvertingRestriction_relativePath_trivialKanFibration`、`IsQCatEquivalence.trivialKanFibration_of_relativePath`、`replacementSquareEndCorner_isQCatEquivalence`、`replacementSquareStartCorner_trivialKanFibration`、`exists_innerPrism_extension_over_fixed_endpoints`、`replacementSquareEndCorner_innerFibration`、`kanEquivalenceLifting_transportSimplexInvertingRestriction`、`IsQCatEquivalence.trivialKanFibration_of_kanEquivalenceLifting`、`trivialKanFibration_replacementSquareEndCorner`、`spanPullbackMap`、`trivialKanFibration_spanPullbackMap_of_left_corner`、`isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting`、`transportSimplexFirstVertexMap_isLocalization_of_isPushout`、`transportSimplexNerveFunctor_preservesColimits`、`transportSimplexInvertingConeIsLimit`、`transportSimplexFirstVertexMap_isLocalization_of_isInitial`、`isPrecompositionEquivalence_discreteConeMap`、`transportSimplexFirstVertexMap_isLocalization_coproduct`、`trivialKanFibration_inverseSequenceConeMap`、`inverseSequencePathDiagram`、`isPrecompositionEquivalence_inverseSequenceConeMap`、`transportSimplexFirstVertexMap_isLocalization`、`transportSimplexInvertingDescentFamilyIso`、`transportSimplexNerveUliftIso`、`transportSimplexFirstVertexMap_ulift_isLocalization`、`leftStraighteningInfinityMap`、`leftStraighteningInfinityMap_restrictIso`、`leftStraighteningInfinityMap_evaluateIso`、`KanEnrichedDiagram.realization_arrow`、`KanEnrichedDiagram.realizationEdge_eq`、`relativeSectionDiagramInfinity_edge`、`leftStraighteningSectionJointDiagram_restrictIso_naturality`、`transportSimplexFirstVertexMap_terminalRestriction`、`transportSimplexFirstVertexMap_initialRestriction`、`relativeFunctorOverPreComparisonEdge_evaluate`、`transportSimplexSectionInfinity_restriction_evaluate`、`leftStraighteningSectionJointDiagram_restriction_evaluate`、`leftStraighteningInfinityMap_firstVertexFiberIso_hom`、`leftStraighteningInfinityMap_edge`、`leftStraighteningInfinityMap_edge_evaluateIso`、`leftStraighteningInfinityMap_edge_hom`、`transportSimplexUnderDomainTransformation`、`relativeSectionRealizationComparisonIso`、`transportSimplexUnderJointIso`、`leftStraighteningInfinityMap_underRealizationIso`、`relativeSectionBaseChangeRealizationIso`、`KanEnrichedDiagramComparison.realizationIso`、`leftStraighteningInfinityMap_firstVertexRestrictionIso`、`leftStraighteningInfinityDiagram_representationIso`、`leftStraighteningInfinityCounit`、`leftStraighteningInfinityMap_isEssentiallySurjective`、`leftStraighteningInfinityReconstruction`、`leftStraighteningInfinityUnitVertex`、`leftStraighteningInfinityMap_baseChangeIso`、`leftStraighteningInfinityPointEquivalence`、`leftStraighteningInfinityMappingComparisonEquivalence`、`leftStraighteningInfinityPinchedHomMap`、`KanEnrichedDiagram.oppositeRealizationIso`、`leftStraighteningCoherentMap_oppositeIso`、`leftStraighteningInfinityMap_firstVertexOppositeIso`、`leftStraighteningInfinityDiagram_firstVertexTransportIso`

### 依存と提供

- Core、Coherent/Quasicategory、Stable/SliceOpposite、HomotopyLimits、KST/Spectra/FibrationTower*、F1B/FullSubcomplexMapping・SSetPullbackAdjoint・QuillenASliceOpposite・Localization・HomotopyWhiskering・RestrictedPrecomposition・FullSubcomplexFunctorFaithful・KanEquivalenceLifting・KanRelativeInternalHomLifting・IntervalFamilyPathParameters は読み取り専用。
- 提供界面は上記の fibration・transport、𝒮・Cat_∞、strict transport の比較。
  𝒮・Cat_∞ の極限・余極限は主張しない。F1e〜F1g は α2b/F1B の担当。
- 再開時は F1/README.md の原典照合と方針を維持し、他レーンのファイルは編集しない。

### 未コミット

- F1/、F1.lean、監査スクリプト、計画は所有ファイルのみ指定して保存する。未コミット実装なし。他レーンの変更は保存・巻き戻しを行わない。

### 既知の問題

- F1 のソースに明示的な `ModelCategory SSet` 仮定はない。モデル構造は使わない。
  `Fibration`・`TrivialKanFibration` はホーン・境界に対する持ち上げ性として用いる。
- strict Kan 図式の strict な Hom が一般に Kan とは主張しない。
  局所 strictification は任意の内面制限と可換でも、境界を固定した構成でもない。
- 各 fiber の同値や辺での一致だけでは図式全体の同型・分類を導けない。
  同値の反映は既証明であり、残る一般の単位・充満忠実性の代わりにはならない。反転関手の単射への制限と同時解像の終点比較の前合成同値の持ち上げは証明済み。局所化比較への適用と単射に沿う pushout での保存も証明済み。余極限の nerve と反転関手の極限表示、空の底の局所化は証明済み。小余積の局所化比較の同値性も証明済み。可算骨格の極限での比較と、任意の底・同じ宇宙の標的への局所化も証明済み。係数を合わせる宇宙持ち上げとの比較と、共同切断評価の降下への適用も証明済み。
- 任意の単射の境界固定延長と高次パラメーターの同時持ち上げは、射影の各次数の fiber が小さい場合に証明済み。
  任意の底上の coherent 空間値図式の unstraightening にも底・パラメーターの小ささを仮定せず適用済み。
  各次数の fiber の小ささを essentially small な ∞ 圏的 fiber のみの条件へ弱める相対延長は未証明。
- 単位・余単位の成分と底変換の自然性は証明済み。任意の小さい底の left fibrations の ∞ 圏から関手 ∞ 圏への leftStraighteningInfinityMap は構成済み。相対表現との対象図式全体の比較・本質的全射性・小さい unstraightening への余単位成分は証明済み。底が ∞ 圏なら実際の復元射と単位同型成分も構成済み。任意の底変換との全対象の両立と一点上の実際の分類同値は証明済み。写像空間の比較同値と実際の分類写像の作用の照合、相対表現との比較の自然性、一般の底の充満忠実性と三角恒等式は未証明。

### 次の一手

次は反転 transport の標準相対表現の全空間側を、全 left fibrations と全相対 Hom のパラメーターで共同実現する。leftCoherentTransportDirectComparison は復元 span を対象ごとに厳密化して選んだ射であり、この選択の自然性は未証明。既存の復元 span と weighted nerve の共同単位を同じ全パラメーターで比較し、選択の代わりに共同族を構成する。係数側は leftStraighteningCoherentMap_oppositeIso で全対象・全高次の比較が完成しているので再証明しない。一般の底へは leftStraighteningInfinityMap_firstVertexOppositeIso と初頂点局所化で戻る。この全空間側の族から leftStraighteningInfinityPinchedHomMap と leftStraighteningInfinityMappingComparisonEquivalence の可換な関手同型を構成し、比較同値を実際の射の充満忠実性へ移す。同じ始域と終域の同値の存在だけから実際の射の同値性を結論しない。自然な単位・余単位と三角恒等式へ進む。
edgewiseEnrichedFunctor は任意の豊穣関手を Hom の共通解像へ移し、右端射影と厳密に自然。KanEnrichedComparison.edgewise と opposite、KanEnrichedDiagram.edgewise と opposite、および左右の豊穣図式比較と realizationIso を構成済み。添字関手による制限は両構成と厳密に可換。leftStraighteningOppositeCoherentMap_vertex は反転族の値が既存 transport の図式全体であることを保証する。nerveStraighteningRepresentationIso は同じ大域的な係数比較の成分を使う。一般の対象図式と表現の主比較は leftStraighteningInfinityDiagram_firstVertexTransportIso と nerveCoherentTransportRepresentationIso を合成して局所化で降下する。
分類同値・既存の単位と余単位への接続・三角恒等式、essentially small な fiber への宇宙の一般化、Cat_∞ 値版は残る。
全体の正本は [foundations.md](foundations.md)。F0 は [infinity-core.md](infinity-core.md)（レーン α）の成果を読み取り専用で使う。

## 0. 目標と範囲

Kerodon 第 5・6・7.3・8 章の内容を、quasicategory の組み合わせ論だけで形式化する。
到達点は (i) straightening/unstraightening の同値（Kerodon Theorem 5.6.0.2）、(ii) 随伴と局所化、
(iii) Kan 拡張、(iv) twisted arrow ∞ 圏と Hom 関手、前層 ∞ 圏 Fun(C^op, 𝒮) と Yoneda 埋め込み。
𝒮 := N^hc(Kan)（γ1 により quasicategory。Kan 複体の内部 Hom が Kan であることは Mathlib の
pushout-product から）。𝒮 の極限・余極限は F2（γ3）に委ね、本レーンでは 𝒮 を対象としてだけ使う。

既存（読むだけ）：A2d の left/right fibration（`Core/RightFibration.lean`）、A3b の Joyal の定理、
A3c〜A3e の写像空間・同値、`Coherent/` の coherent nerve。

## 1. 工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| F1a | cocartesian/cartesian 辺と fibration の定義、inner fibration との関係、left/right fibration との関係、合成・底変換での閉性、fiber が quasicategory | Kerodon 5.1 / HTT 2.4.1–2.4.2 |
| F1b | covariant transport：cocartesian fibration の辺に沿う fiber 間の関手、その一意性（可縮な選択空間）、ホモトピー圏への降下 | Kerodon 5.2 / HTT 2.4.4 |
| F1c | Cat_∞ := N^hc(QCat)（Kan 複体 core を Hom に取る単体的圏の coherent nerve。core は A3b の可逆辺）と Fun(C, Cat_∞) | Kerodon 5.5 / HTT 3.0 |
| F1d | **straightening**：cocartesian fibration U → N(C)（まず C が通常の圏）と関手 N(C) → Cat_∞ の対応、unstraightening の構成、同値（Theorem 5.6.0.2）。left fibration と 𝒮 値関手の場合を先に | Kerodon 5.6 / HTT 2.2.1.2、3.2 |
| F1e | 随伴（単位・余単位、写像空間での特徴づけ）、随伴関手の合成、Kan 拡張との関係 | Kerodon 6.1–6.2 / HTT 5.2 |
| F1f | 局所化 C → C[W⁻¹] の普遍性（Kerodon 6.3）と反射的部分 ∞ 圏 | Kerodon 6.3 / HTT 5.2.7 |
| F1g | 左右 Kan 拡張（点ごとの公式、存在と一意性）、cofinality の一般形（Quillen A） | Kerodon 7.2–7.3 / HTT 4.1.3、4.3 |
| F1h | twisted arrow ∞ 圏 Tw(C)、Hom 関手 C^op × C → 𝒮（F1d の left fibration 版で straighten）、前層 ∞ 圏 P(C) := Fun(C^op, 𝒮)、Yoneda 埋め込み、充満忠実性、表現可能関手と極限 | Kerodon 8.1–8.3 / HTT 5.1.3 |
| F1i | 検査：通常の圏の nerve で F1d・F1h が古典（Grothendieck 構成、Yoneda）に戻ること | — |

**分割（2026-10-18 15:40）：** F1e・F1f・F1g は straightening に依存しないので、レーン α2b（Π2 チャット、
計画は [infinity-core-F1b.md](infinity-core-F1b.md)、配置 `InfinityCategories/F1B/`）へ切り出した。
α2 の順序は F1a → F1b → F1c → F1d → F1h → F1i。F1h は α2b の Kan 拡張を使ってよい。F1d が最大の山で、
Kerodon 5.6 の証明（5.3 の「fibration の ∞ 圏」、5.4 の （∞,2）的道具を避ける経路）を
着手前に照合し、文言と証明方針を `Core/README.md` ではなく `InfinityCategories/F1/README.md` に記録する。

## 2. 設計上の決定

- 配置は `SerrePositivity/InfinityCategories/F1/`、namespace `SerrePositivity.InfinityCategories`。
  集約 `InfinityCategories/F1.lean` をルートに 1 行で追加する。
- fibration は `MorphismProperty.rlp` 流儀で定義し、A2d の left/right fibration と整合させる。
- Cat_∞ と 𝒮 は coherent nerve で定義する（γ1）。両者の極限・余極限は F2 まで主張しない。
- straightening は left fibration・𝒮 値の場合を先に完成させ、cocartesian・Cat_∞ 値へ拡張する。
- モデル構造（covariant/contravariant model structure）は使わない。Cisinski 流の代替は採らない。
- sorry・公理・引用は導入しない。実施記録はコミットメッセージ、宣言名と型の一覧は本文書 §3。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1-log.md](archive/infinity-core-F1-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
