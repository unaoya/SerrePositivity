# F2：F2-lite と presentable ∞ 圏（v2、F1b）

作成日：2026-10-18。更新日：2026-10-23。
正本は [foundations.md](foundations.md)。本書は F2-lite と F2 後半の正本。
F1b の前提工程は [infinity-core-F1b.md](infinity-core-F1b.md)、
N の γ3・γ4 は [e-infinity-algebras.md](e-infinity-algebras.md) を参照する。

## 引き継ぎ（2026-10-23）
### 現在地

- 第 1 部（B4・B5、F2L-1〜4）は完了。coherent nerve の Cat_∞、引き戻しと lax pullback、
  写像空間の普遍性、同値矢印の全部分圏との比較、安定性と完全な両射影まで証明済み。
- 第 2 部の正本は §3。10-23 改訂：F1b は a7 のみ。F2N-2・5 は F1、F2N-3・4 は N。
  正則 κ の小さい join・coslice、filtered 性と coslice の弱可縮性・対角の cofinality の双方向判定を証明。
  通常 filtered 図式の有限内部 Hom・path 引き戻しの交換、元の標準余錐の native 余極限性を証明。
  小さい底上の任意の coherent 空間値図式の HasColimit は全空間模型と元の単位から構成。
  元の全空間 Kan 積・引き戻し比較の弱同値性とホモトピー逆を証明。
  境界固定の相対有限検出・同時輸送・反映、境界移動の除去は元の値・円柱を保持。
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。
  a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合まで完了。
  a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全単体の交換、
  形状接着の錐空間の native 極限性、finiteShape_cell_induction を整備済み。
  coherentColimitFunctor は元の全空間頂点・native 余錐を保ち、指定各点余錐による完成と全錐の像を比較。
  元の単位三角柱の三三単体・共有面・上下二面・六側面と、全係数 EF⊗K の実 pointed 持ち上げを保持。
  元の指定三角形比較の二辺・長辺を同じ普遍 prism へ厳密に回収し、全 prism 比較の指定自然性を証明。
  元の相対三角形比較の前合成を、同じ全実三角形の三辺の指定比較で値まで同定。
  六共有辺の実 prism・実始点・実終点・指定比較を保ち、四面を同じ共通四頂点と六比較へ正規化。
  CoherentColimitUnitTetrahedronBoundary.comparison_square は同じ全族の四面の厳密な可換性。
  二内部三角形は元の三単体の実共有面そのもの。元の定値余極限三角形・外側六面を保持して境界を構成。
  三つの coherentColimitUnit{First,Middle,Last}TotalRelation は同じ元の全空間・恒等初期値上の指定関係。
  coherentColimitUnitTriangleValue_coherence は二内部面を消去した元の上下二面・指定対角の整合式。
  元の五因子全式を同じ固定 native 値へ写し、実三頂点・元の模型三角形を保って a6 の区間比較式へ代入済み。
  模型三角形式の下側輸送・上側単位を消去。残りの像を同じ raw fiber 二面比較の最後辺輸送で回収し、最初辺の元の模型比較への同じ射影と反映判定を証明。
  第一辺の模型比較への反映・最後辺輸送と四因子境界式は構成済み。全反転 Hom の pointed 族と元の raw 普遍三角形の始点固定比較を構成。
  pointedHomTriangleLongEvaluationComparison_eq_morphism / CompositeEvaluationComparison_eq_morphism は元の長辺・二辺評価比較を同じ固定射の比較へ同定。spaceCompositionZero_morphism_coherence は元の指定零面・精密化・値と三射の固定比較の整合式。元の全実長辺と固定射の実 prism は PointedMorphismPrismEquality / CoherentColimitApexLongMorphismPrism で一致。NativeComparison.postcomp V₂ と固定射の元の ValueComparison は CoherentColimitApexLongFixedValue で値まで一致。RawLongValueIso.precomp q の canonical 表示と移送初期係数の標準表示は CoherentColimitApexRawLongCanonical。coherentColimitApexLongRawValueRatio_heq_evaluation は同じ raw 値比較の逆と指定普遍比較の値の合成を元の右評価成分へ回収。coherentColimitApexLongRawValueRatio_cancel は raw 値比較と同じ比の合成を元の指定普遍比較へ厳密に回収。coherentColimitApexLongValueComposite_trans_ratio は元の LongComparison と raw 長辺値比較の合成に同じ比を続けると元の NativeComparison の値になることを証明。三つの実頂点の値を CoherentColimitApexLongValueVertices で照合し、coherentColimitApexLongEvaluationComparison_heq_value_composite は元の全三角形の長辺評価比較 Nlong を同じ実長辺比較と raw 長辺値比較の合成へ値まで同定（元の実結合表示は functorIsoOfEq で保持）。長辺評価の因子式は完了。relativePrismSpecified_naturality は始点も動く二実 prism の元の指定対角比較に対する可換正方形。全相対関手 R 上の同じ実評価 prism を比較・curry して構成し、一点成分は relativePrismDiagonalComparison_at_vertex で元の指定値へ回収。relativePrismActualEndpointIso_restrict_heq は辺制限後の実終点像と同じ全図式の終点評価の指定像の一致。relativePrismNativeEndpointIso_heq_initial_postcomp は固定区間の native 終点像を同じ実始点比較の同じ普遍輸送による後合成へ値まで同定。relativePrismEndpointImage_restrict_heq は同じ辺の両端像を元の全端点評価へ回収し、実始点表示は relativePrismInitialEndpointIso_restrict_heq。CoherentColimitApexPointedLastPrism は元の全初点係数を保つ最後辺の実始点・終点・底を保持し、projection_constant は底を元の raw 区間頂点の定値族へ厳密に同定。coherentColimitApexPointedLastConstantIso は元の PointedLastIso と値まで同じ固定区間上の比較。coherentColimitApexLastSpecified_naturality は元の最後辺の二実 prism・実両端・同じ指定比較の自然性正方形。coherentColimitApexLastNative_heq_initial_postcomp はその同じ native 像を実始点比較の普遍輸送による後合成へ同定。coherentColimitApexLastInitialEndpointIso_eq_middle / coherentColimitApexLastActualEndpointIso_eq_target はその実始点・終点像を元の全三角形の中間・終点比較へ厳密に同定。coherentColimitApexLastSpecified_endpoint_square / coherentColimitApexLastNative_heq_middle_postcomp は同じ正方形をその元の二比較で表示。spaceCompositionZeroFamily_last_eq_original は零面の実最後辺と元の最後辺の一致、middle/target_eq_original は同じ共有辺の両端作用の一致。spaceCompositionZeroFamily_first_eq_standard は退化した実初辺の一致。spaceCompositionZeroMiddleEndpointIso_eq_refl は同じ指定中間像の恒等性。relativePrismNativeEndpointIso_heq_initial_action / eq_refl_of_initial は全区間族の native 作用の始点評価への因数分解と恒等性の移送。未完：これらを零面の同じ最後辺制限比較に適用し、Ncomp の零面・終点比較・二 raw 辺値比較との値照合、spaceCompositionZero_morphism_coherence への二式の代入と零面値の消去による長辺値式、全錐比較と保存性。
  未完：同じ長辺輸送の残りと raw 二面比較の像の全区間族への照合・反映、二三角形・指定 path の全錐比較、引き戻し保存、
  部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。
  F1b は a7 のみ担当。完了時は F1 の交換入力に合う定理を公開し、次の割り当てを待つ。
  検証：三集約同時ビルド10372 jobs、公理監査19484宣言（標準三公理のみ）、F1/F1B 同時 import 16331/5164宣言成功。
  追加11モジュール20明示宣言：零面の初辺の厳密一致、元の指定中間点像の恒等性、全区間族の native 作用の始点評価への因数分解と指定始点像の恒等性からの native 像の恒等性。

### 残り（依存順、実作業時間の概算）
- F2N-1：𝒮 の一般 coherent filtered 余極限と有限極限との交換。全空間模型の native 余極限性は証明済み。
- F2N-2（F1）：前層内の Indκ、生成と保存関手の延長の普遍性。F2/Ind/・Ind.lean は読み取り専用。
- F2N-3（N）：compact・Yoneda・retract、30〜80 時間。F2N-4（N）：冪等完備化、所有外。
- F2N-5（F1）：Ind(C) の安定性、冪等完備 C の compact 生成。40〜100 時間。
- その後 F2 後半：presentable と随伴関手定理（担当は次の割り当て待ち）。HTT §5.5、Kerodon 9。細分化は §4。
  Bousfield 局所化・P_Σ は従来どおり N の I-b の範囲。

### 主要宣言（検証済みのみ）

- `F2.IsKappaSmall` / `F2.IsFilteredInfinity` / `F2.IsKappaFiltered` / `F2.isKappaSmall_aleph0_iff` / `F2.isKappaFiltered_aleph0_iff` / `F2.isFilteredInfinity_of_retract`
- `F2.isKappaSmall_join` / `F2.isKappaFiltered_sliceUnder` / `F2.isFilteredInfinity_iff_isContractibleKan` / `F2.cosliceCoproduct_isPullback` / `F2.isRightCofinal_sliceUnderProjection_of_filtered`
- `F2.laxCosliceDiagonalCommaIso` / `F2.weaklyContractible_diagonalStandardComma_iff` / `F2.isFilteredInfinity_iff_of_equivalence` / `F2.isKappaFiltered_iff_of_equivalence`
- `F2.reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered` / `F2.filteredKanColimitComparison_factor` / `F2.filteredKanColimitCocone_isColimit`
- `F2.kanCoconeAugmentationComparison_factor` / `F2.filteredKanColimitOrdinaryCocone_isColimit` / `F2.intervalReplacementColimitIso` / `F2.intervalPullbackColimitIso`
- `F2.intervalPullbackCone_isLimit` / `F2.filteredIntervalPullbackExchange` / `F2.continuousKanLeftFibration_pair_relative_detection` / `F2.totalKanProductComparison_homotopyEquivalence`
- `F2.continuousKanLeftFibration_finite_relative_detection` / `F2.continuousKanLeftFibration_finite_boundary_detection`
- `F2.coherentSmallConstantTargetMap_isQCatEquivalence` / `F2.coherentDiagramTotalCocone_vertex`
- `F2.coconeTransformationMap_prism` / `F2.coconeTransformationMap_isQCatEquivalence`
- `F2.coherentCoconeTotalComparison_homotopyEquivalence` / `F2.coherentTotalCoconeUnitIso`
- `F2.unstraighteningMappingTriangleIso` / `F2.coherentTotalUnitHomComparison_homotopyEquivalence`
- `F2.coherentDiagramTotalCocone_isColimit` / `F2.hasColimit_coherentSpaceDiagram`
- `F2.exists_relativePathFiniteModelTransport` / `F2.relativePath_model_reflection`
- `F2.laxPullbackFst_isExactFunctor` / `F2.laxPullbackSnd_isExactFunctor` / `F2.laxPullback_isStable`
- `F2.fiberwisePullbackNativeCone_isLimit` / `F2.fiberwisePullbackCone_projection_commutativity` / `F2.fiberwisePullbackTotalRawPathHomotopy_curry` / `F2.coherentTotalMapNativeFiberTransportIso` / `F2.coherentTotalMapNativeValueIso` / `F2.coherentTransformationNativeCoconeIso` / `F2.coherentCospanConeNativeComparison` / `F2.coherentCospanConeValuePathHomotopy_unit` / `F2.coherentCospanConeTotalModelComparison_over_base` / `F2.coherentCospanConeTotalModelFiberComparison_path_ι` / `F2.coherentCospanConeRelativeValuePathIso_eq` / `F2.coherentCospanConePointwiseCone_vertex` / `F2.coherentCospanConePointwiseCone_leftTriangle` / `F2.unstraighteningMappingTrianglePrism` / `F2.coherentTransformationTriangleLift_long` / `F2.coherentTransformationPointedTriangle_projection` / `F2.relativeExtensionRestriction_vertex` / `F2.prismExtensionComparison_restrict` / `F2.coherentTriangleExtensionComparison_restrict` / `F2.coherentTriangleExtensionRestriction_long` / `F2.relativeFunctorBaseChangeInverse_overPre` / `F2.prismExtensionPullbackEndpoint_restrict` / `F2.prismExtensionPullbackComparison_restrict` / `F2.relativeFunctorCurryHom_pre` / `F2.relativeFunctorCurryHom_evaluate` / `F2.prismExtensionCurryWitnessIso_restrict` / `F2.unstraighteningSourceComparisonIso_app_pre` / `F2.coherentTriangleCurryIso_restrict` / `F2.unstraighteningTriangleRelativeVertexIso_pre` / `F2.coherentSmallTriangleRelativeIso_pre` / `F2.unstraighteningTriangleRelativeVertexIso_pre_eq` / `F2.coherentSmallTriangleRelativeIso_pre_heq_endpoint` / `F2.coherentSmallFiberPointedTriangle_projection` / `F2.coherentSmallTriangleRelativeIso_pre_eq_endpoint` / `F2.coherentTransformationTriangleFiberIso_heq_endpoint` / `F2.relativeIsoFiberHomotopy_hom` / `F2.coherentCospanConeFiberComparisonPathIso_eq` / `F2.coherentCospanNativeSectionFiberPathDownIso_eq_native` / `F2.coherentCospanModelFiberPathIso_eq_section_down` / `F2.coherentCospanNativeFiberCospanEndComparison_homotopyEquivalence` / `F2.coherentCospanNativeSectionEndComparison_homotopyEquivalence` / `F2.strictPullback_functorIso_exists` / `F2.kanHomotopyRectificationIso_image` / `F2.coherentCospanNativeLeftLegFinalImage_heq` / `F2.functorIsoDown_injective` / `F2.coherentCospanNormalizedModelPathLiftIso_eq_section` / `F2.coherentCospanCommonLeftIso` / `F2.coherentCospanCommonRightIso` / `F2.intervalReplacementSectionIso_endpoint` / `F2.coherentCospanConeNativePathDownIso_whisker` / `F2.coherentTotalNativeKanIso_postValueImage` / `F2.coherentCospanCommonRightImage` / `F2.cospanRectificationLeftIso_inverse_image` / `F2.coherentCospanNativeFirstPathIso_heq` / `F2.coherentCospanModelFirstPathIso_heq` / `F2.coherentCospanCommonComparisonIso` / `F2.coherentCospanConeNativeComparison_homotopyEquivalence` / `F2.coherentCospanConeNativeComparison_isWeakHomotopyEquivalence` / `F2.coherentCospanNativeLimitCone` / `F2.coherentCospanNativeLimitCone_isLimit` / `F2.coherentCospanNativeLimitCone_vertex` / `F2.coherentCospanNativeLimitConeFstIso` / `F2.coherentCospanNativeLimitConeSndIso` / `F2.coherentCospanNativeLimitCone_projection_commutativity` / `F2.coherentFilteredColimitVertex_isTerminal` / `F2.coneMappingShapePushoutIso` / `F2.coneMappingShapePushout_right_fibration` / `F2.coneMappingShapePushoutNativeCone_isLimit` / `F2.finiteShape_cell_induction` / `F2.CoherentFilteredLimitExchangeShape` / `F2.coherentColimitFunctor` / `F2.coherentCompletedLimit_iff_colimitFunctor` / `F2.coherentCospanOfFunctorTriangles` / `F2.functorCospanNativeLimitCone_isLimit` / `F2.exists_limitFamilyRestrictionTriangle` / `F2.coneFamilyReindex_apex` / `F2.exists_limitConeFamilyReplacement` / `F2.HasSpaceLimitsOfShape` / `F2.coherentFilteredLimitExchangeShape_simplex` / `F2.coherentFilteredLimitExchangeShape_of_empty`

- `F2.coherentColimitUnitValueAction_coherence` / `F2.coherentColimitUnitValueAction_total_heq_native` / `F2.coherentColimitUnitValueAction_precomp_firstEdge`
- `F2.coherentColimitApexRawTriangleBoundaryAt` / `F2.coherentColimitApexRawTriangleBoundaryAt_precomp` / `F2.coherentColimitApexRawTriangleCandidate_eq_universal_iff` / `F2.spaceSimplexPointedLift` / `F2.spaceSimplexPointedLift_projection` / `F2.spaceSimplexPointedFamily` / `F2.coherentColimitApexCoefficientMap` / `F2.coherentColimitApexPointedFamilyComparisonIso` / `F2.coherentColimitApexPointedFamilyRestrictionIso` / `F2.coherentColimitApexPointedFirstIso` / `F2.coherentColimitApexPointedLastIso` / `F2.coherentColimitApexPointedLongIso` / `F2.pointedCoherentSourcePrecomposition_fixed` / `F2.spaceTrianglePointedFamily_middle_action` / `F2.spaceTrianglePointedFamily_target_action` / `F2.coherentColimitApexMiddleCoefficientMap` / `F2.coherentColimitApexTargetCoefficientMap` / `F2.coherentColimitApexPointedMiddleEndpointIso` / `F2.coherentColimitApexPointedTargetEndpointIso` / `F2.coherentColimitApexPointedLongComparison` / `F2.coherentColimitApexPointedTargetEndpointIso_eq_longEndpointComparison` / `F2.coherentColimitApexPointedTargetEndpointIso_trans_universal` / `F2.coherentColimitRawUniversalTriangleComparison_precomp` / `F2.coherentColimitApexRawUniversalBoundary_iff_coefficient` / `F2.coherentColimitApexRawTriangleCandidate_eq_universal_iff_long_value` / `F2.pointedValueRightComparison_triangle` / `F2.pointedValueRightComparison_triangle_inverse` / `F2.pointedFiberValueToRightEquivalence` / `F2.pointedFiberValueTo_triangle_at` / `F2.pointedFiberValueTo_triangle_inverse_at` / `F2.pointedRightFamilyTransportIso_precomp_heq` / `F2.pointedRightFamilyTransportIso_heq_universal` / `F2.pointedRightFamilyTransportIso_action_square` / `F2.pointedRightFamilyTransportIso_counit_square` / `F2.pointedValueFamilyTargetCounitIso_conjugation` / `F2.pointedValueFamilyTransportIso_at_right` / `F2.spaceCompositionZeroPointedHomotopy_projection` / `F2.spaceCompositionZeroPointedHomotopy_initial` / `F2.spaceCompositionZeroExtensionPath_uncurry` / `F2.spaceCompositionZeroCylinderIso_eq_comparison` / `F2.spaceCompositionTetrahedronZeroComparison_hom_eq_cylinder` / `F2.spaceCompositionZeroComparison_endpoint_hom` / `F2.spaceCompositionZeroEndpointEdge_action` / `F2.spaceCompositionZeroCosliceEndpointFiber` / `F2.spaceCompositionZeroCosliceEndpoint_refinement` / `F2.coherentKanRefinement_original_square` / `F2.coherentKanRefinement_value_square` / `F2.pointedValueTriangleIntervalImage_iso` / `F2.pointedLeftHomValueActionIso` / `F2.pointedHomRefinement_value_coherence` / `F2.pointedHomTriangle_value_coherence` / `F2.spaceCompositionZeroValueIso_heq_endpoint` / `F2.spaceCompositionZero_evaluation_coherence` / `F2.coherentColimitApexCoefficientMap_value` / `F2.coherentColimitApexMiddleCoefficientMap_value` / `F2.coherentColimitApexTargetCoefficientMap_value` / `F2.pointedHomMorphismEvaluationComparison` / `F2.pointedHomTriangleLongEvaluationComparison_eq_morphism` / `F2.pointedHomTriangleCompositeEvaluationComparison_eq_morphism` / `F2.spaceCompositionZero_morphism_coherence` / `F2.coherentKanMorphismIntervalComparison_heq_refl` / `F2.pointedHomMorphismValueComparison_eq_left` / `F2.pointedHomMorphismEvaluationComparison_factor_left` / `F2.pointedCoherentMorphismPrism` / `F2.coherentColimitApexPointedLongPrism_heq_morphism` / `F2.pointedReverseMorphismPrism` / `F2.pointedReverseMorphismPrism_coordinates` / `F2.pointedCoherentMorphismPrism_coordinates` / `F2.pointedMorphismPrism_obj` / `F2.coherentReverseThickening_initial_map` / `F2.coherentReverseComposition_initial_transport` / `F2.pointedMorphismPrism_simplex_eq` / `F2.pointedCoherentMorphismPrism_eq_reverse` / `F2.coherentColimitApexPointedLongPrism_heq_reverse` / `F2.pointedLeftHomValueActionIso_app_heq_fixed` / `F2.pointedHomMorphismValueComparison_heq_prism` / `F2.fiberTransportDiagonalIso_postcomp_precomp_heq_prism` / `F2.pointedReverseDiagonalPrism_fixed_eq_coherent` / `F2.diagonalUniversalPrism` / `F2.leftFibrationPrism_diagonalTransportIso_precomp_eq_witness` / `F2.pointedIntervalTransportAt_universalIso_heq_endpoint` / `F2.pointedParametrizedTransportPullback_point_prism` / `F2.pointedIntervalUniversalSource_comparison_trans` / `F2.coherentColimitApexPointedLongComparison_trans_universal` / `F2.coherentColimitApexPointedLongNativeComparison_heq_diagonal` / `F2.leftFibrationPrism_diagonalTransportIso_precomp_heq` / `F2.diagonalTransportIso_heq_of_boundary` / `F2.coherentColimitApexPointedLongNativeComparison_post_value_heq_morphism` / `F2.coherentColimitApexRawLongValueIso_precomp_heq_standard` / `F2.coherentColimitApexCoefficientMap_standard` / `F2.coherentColimitApexLongEvaluationComparison_heq_value_composite` / `F2.coherentColimitApexLongValueComposite_trans_ratio` / `F2.coherentColimitApexLongRawValueRatio_heq_evaluation` / `F2.relativePrismSpecified_naturality` / `F2.relativePrismDiagonalComparison_at_vertex` / `F2.relativePrismActualEndpointIso_restrict_heq` / `F2.relativePrismNativeEndpointIso_heq_initial_postcomp` / `F2.relativePrismInitialEndpointIso_restrict_heq` / `F2.coherentColimitApexPointedLastPrism_projection_constant` / `F2.coherentColimitApexLastSpecified_naturality` / `F2.coherentColimitApexLastNative_heq_initial_postcomp` / `F2.coherentColimitApexLastInitialEndpointIso_eq_middle` / `F2.coherentColimitApexLastActualEndpointIso_eq_target` / `F2.coherentColimitApexLastSpecified_endpoint_square` / `F2.spaceCompositionZeroFamily_last_eq_original` / `F2.spaceCompositionZeroMiddleEndpointIso_eq_refl` / `F2.relativePrismNativeEndpointIso_eq_refl_of_initial`

### 依存と提供

- N の HomotopyLimits（γ3c の 𝒮 の余極限）と F1 の straightening は読み取り専用。
  γ4 は前提として一括仮定せず、必要な公開界面と提供済みの範囲を確認する。
- 第 1 部を D・K へ提供済み。F1 へ全有限 K の CoherentFilteredLimitExchangeShape K を提供予定。compact は N、Ind の安定性は F1。

### 未コミット
- 所有ファイルの未コミットなし。本区切りの F2 直下 11 モジュール・集約・監査・両計画を同じパス限定コミットで保存。コンパイルしない作業中ソースなし。共有ツリーの他レーンの変更は対象外。/tmp の試行ファイルは再開に不要。

### 既知の問題

- F1 の前層・Yoneda は F1 計画の後続工程。Ind の存在を仮定して回避しない。F1B の intervalMinimum 複製は straightening 非依存の F1.IntervalMinimum import に置換。衝突ゼロ。 前回の依存停止は R の共有ツリーの一時変更と判明、10-23 09:58 に取り消し・元の olean を再構築済みとの連絡。再実行中の ScaffoldFiniteCylinderEndpoints の生成物不在も単独ビルド 1929 jobs で回復、対象 F2.SpaceCompositionZeroFirstPrism は 2881 jobs で成功（/tmp/f2-zero-first-prism-resume-confirmed.log）。R は今後別 worktree。今回の再ビルド・両監査は成功し、現存する import 閉包の破損なし。
- 一般の coherent な図式の余極限と、通常の小圏による strict 図式の余極限を区別する。
- 既存 anodyneKanObject の保存性を仮定せず、連続な Q と単位の anodyne 性・弱同値性を具体的に証明。
  通常の指定余錐の全脚・高次の整合性を保持した native な普遍性まで証明済み。
  任意の二射の元の cospan の native な極限との比較は証明済み。一般 coherent filtered 図式の交換は残る。
  全空間模型の余錐全体・頂点・単位との比較は構成済み。余錐空間の比較同値と元の単位との同型は証明済み。
  元の全空間余錐への全 Hom 判定の適用は完了。必要な fiber 標的を明示し、小さい単位の比較から証明。
- 主経路に追加公理・sorry・ModelCategory SSet の instance 仮定を置かない。

### 次の一手

- F2N-1 a7：まず SpaceCompositionZeroMiddleIdentity / RelativePrismNativeInitialIdentity を読む。零面の最後辺への同じ指定制限比較の始点像を spaceCompositionZeroMiddleEndpointIso に同定し、恒等性を native 終点像へ送る（以下の具体手順）。a7 は未完。
  coherentColimitApexCoefficientMap は全反転 Hom から元の実初点 fiber への同値で包含を保持。
  coherentColimitApexPointedFamilyComparisonIso は元の raw 普遍三角形と spaceSimplexPointedFamily を同じ図式・初点を固定して比較する。
  PointedFirst/Last/LongIso は三面を元の実 prism に同定済み。RestrictionIso_precomp/shared と initial は二段制限・共有制限・初点の整合。
  三頂点の作用は SpaceTrianglePointedVertexActions で計算済み。Middle/TargetCoefficientMap は元の実 fiber 内の同じ全係数作用。
  PointedMiddle/TargetEndpointIso は同じ全比較の終点像。PointedLongTransport は δ₁ ▷ A ≫ spaceSimplexPointedFamily s と同じ実両端を持つ元の長区間の輸送証人。
  次の値照合は RawTriangleCandidate_eq_universal_iff_long_value の右辺：TargetEndpointIso.postcomp V₂ ≪≫ RawTriangleBoundaryAt B T q = PointedLongComparison.postcomp V₂。Nlong は coherentColimitApexLongEvaluationComparison_heq_value_composite で完了。Ncomp の零面値 ≪≫ PointedTargetEndpointIso.postcomp V₂ ≪≫ 二辺評価（元の RawLastValueIso・RawFirstValueIso の二因子）は未完。零面の元の指定中間像 spaceCompositionZeroMiddleEndpointIso_eq_refl は完成。具体的に M=coherentSimplexMaximalization s、A=元の全初点係数、r=δ₀▷A、β=r≫(fst Δ[2] A≫Yoneda M)、W=r≫family M、W′=r≫ZeroFamily、e=spaceCompositionTetrahedronZeroRestrictionIso s r と置く。始点の添字式 endpoint₀≫r=simplexPrismVertex 2 1 A と spaceCompositionZeroMiddleMap_standard/zero、spaceCompositionZeroMiddle_base で両実始点と底を揃える。spaceSimplexPointedRestrictionEndpointImage_heq_endpoint の i=0 と vertexIsoOfEq_heq により relativePrismInitialEndpointIso e を同じ spaceCompositionZeroMiddleEndpointIso s に厳密同定する。終点の底は SpaceCompositionZeroEndpointAction の spaceCompositionZeroEndpoint_base。relativePrismNativeEndpointIso_eq_refl_of_initial を適用し、同じ e の native 像を恒等にする。relativePrismSpecified_naturality の正方形から零面の実終点像 ≪≫ 元の最後辺の指定対角比較 = 最大化側の最後辺の指定対角比較を得る。W′ は spaceCompositionZeroFamily_last_eq_original で元の実最後辺に厳密一致。終点像は同じ汎用制限端点補題を i=1 で用いて元の零面値へ接続する。Apex 側の実最後辺の指定正方形は coherentColimitApexLastSpecified_endpoint_square、native 中間像は coherentColimitApexLastNative_heq_middle_postcomp で完成済み。coherent 合成四角形、pointedValueFamilyTransportIso_at_right と元の単位・余単位三角式で最大化側の比較を同じ二辺評価へ戻し、最後辺の raw 値比較を functorIso_whisker_exchange で同じ中間比較に沿って移す。元の RawLastValueIso・RawFirstValueIso を保持し Ncomp を独立に証明する。Nlong/Ncomp を spaceCompositionZero_morphism_coherence に代入し同じ零面値を消去、目標の長辺値式へ戻す。全零面・δ₀ 面の係数は元の s.obj 0。TargetEndpointIso_trans_universal や反映判定を未証明の値式の代用にしない。raw な全 ΦZero の中間像を直接 HEq の型に展開する補題は200k whnfに達したため採用せず、同じ値を保つ正規化端点と汎用制限補題を使う。資源上限は変更なし。
  δ₀ の面の係数は元の s.obj 0 のまま保持する。RawUniversalBoundary_iff_coefficient と of_long_value は、値照合から恒等初期値と任意の全初期値への忠実な反映を証明済み。反映を未証明の値式の代わりに使わない。
  RawUnitFiberComparison_eq_iff_model は元の最初辺模型比較への同じ射影で raw 比較を反映する。未完：長辺輸送の残りとの合成を同じ全族の三辺・指定三角形へ戻す。
  同じ余錐 fiber 写像の前合成の充満忠実性で整合を反映し、二三角形・指定 path を保つ全錐比較を束ねる。
  その極限性から引き戻し保存へ接続。値の整合式・辺ごとの同型だけでは全錐比較の完了としない。
  続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction。
  HTT §5.3.3、a7 残り12〜24時間（暫定。三角形に沿う全指定因子の照合に不確実性）。strict 図式だけでは完了としない。
  a7 後は全有限 K の CoherentFilteredLimitExchangeShape K を公開し、F1 の IndFiniteLimitExchangeInput.exchange に渡せることを確認して報告、次の割り当てを待つ。

## 0. 目標と範囲

| 工程 | 担当 | 到達点 | 原典 |
| --- | --- | --- | --- |
| F2L-1 | F1b | 完了：Cat_∞ の対象・辺・関手 core との写像空間比較、関手の同値の判定 | Kerodon §5.5.3 |
| F2L-2 | F1b | 完了：Cat_∞ の引き戻し、全試験写像空間の普遍性、二射影と指定 path の同時比較 | Kerodon §5.5.3、HTT §3.3.3 |
| F2L-3 | F1b | 完了：lax pullback、対象三つ組、native 極限錐、全試験関手 core、Remark 6 の写像空間の 𝒮 内の極限性 | Tamme §1 Definition 5・Remark 6 |
| F2L-4 | F1b（D と接続） | 完了：通常の引き戻しとの比較、安定性・完全な両射影、極限・余極限の成分判定 | Tamme §1 Remark 7・Lemma 8 |
| F2N-1〜5 | F1b（1 a7）、F1（2・5）、N（3・4） | filtered、Ind、compact、冪等完備化、Ind の安定性 | HTT §5.1.4・§5.3、Kerodon 9 |
| F2 後半 | 本レーンの担当外（foundations.md の分担による） | presentable、随伴関手定理、Bousfield 局所化、P_Σ | HTT §5.5、Kerodon 9 |

F2-lite の範囲に presentable・Pr^L のテンソル積・HA §4.8 は含めない。
Tamme の分裂定理・Verdier 列・Land–Tamme の主定理は K-基盤、dg gluing との比較は D の β4。

## 1. 設計と受入条件

- 新規配置は `SerrePositivity/InfinityCategories/F2/`。F1 の既存公開名を保持する。
- 宇宙：小 ∞ 圏の単体は `SSet.{u}`、`CatInfinity.{u}` は `SSet.{u+1}`。
  Cat_∞ 内の図式と、元の小 ∞ 圏間の関手の宇宙を明示する。
- `CatInfinity = SimplicialNerve QCat`、QCat の Hom は `core Fun(C,D)`。
  Hom に全ての自然変換を含む模型は別の構造なので代用しない。
- Cat_∞ の引き戻しの構成では、対象と射の表示に加えて、全ての試験 ∞ 圏からの
  写像空間が空間の引き戻しを与えることを証明する。hCat だけの普遍性で完了としない。
- `p : A → C`、`q : B → C` に対し、lax pullback は
  `(A × B) ×_(C × C) Fun(Δ¹,C)`。端点評価は `(source,target)`、矢印は `p(a) → q(b)`。
  元の引き戻しは、矢印が同値である対象の張る全部分 ∞ 圏として比較する。
- 単体集合の strict pullback が使える箇所では、端点評価の充填性と、その strict pullback が
  Cat_∞ の引き戻しを表すことを証明してから使う。
- 安定性は有限極限・有限余極限と exact 関手の保存を通じて接続し、
  dg gluing との比較・分裂定理を定義のフィールドとして仮定しない。
- 追加公理・sorry・文献入力は導入しない。許す公理は標準三公理のみ。
  新しい主経路に `ModelCategory SSet` 等の instance 仮定を置かない。
- 保存単位ごとに対象ビルド、公理監査、主経路の instance 仮定の検索を実施。
  検証済みの構成・普遍性・比較の範囲を別々に現在地へ反映する。

## 2. 原典

- [Kerodon §5.5.3](https://kerodon.net/tag/0208)：QCat の coherent nerve と ∞ 圏の ∞ 圏。
- [Kerodon Proposition 5.5.3.3](https://kerodon.net/tag/020B)：局所 Kan 性からの quasicategory 性。
- [Tamme 2018 §1](https://arxiv.org/html/1703.03331v3#S1)：Definition 5、Remarks 6–7、Lemma 8。
  Remark 6 の四角形は [PDF 第 5 頁](https://arxiv.org/pdf/1703.03331v3#page=5) で確認する。
- HTT §3.3.3（∞ 圏の極限）、§5.3（Ind・compact）、§5.5（presentable）。
- [Kerodon §4.9.4](https://kerodon.net/tag/03S1) の κ-small、[§9.1.1](https://kerodon.net/tag/02P8) の filtered ∞ 圏。
  9.1.1.16 の正則 κ 版 coslice、9.1.1.17 の弱可縮性、9.1.1.18 の対角判定、9.1.1.19 の同値不変性、9.1.1.20 の Kan 判定を証明済み。

## 3. F2-lite 第 2 部（10-22 12:35 分担改訂）

### 引き継ぎ（F1b：F2N-1 a7、F1：F2N-2・5、N：F2N-3・4）

- 現在地：F1b は a7 のみ。Ind・F2N-5 は F1、compact・冪等完備化は N。第 1 部は完了済み。
  F2N-1 は正則 κ の小さい join・coslice、一般の弱可縮性、対角関手の cofinality とその逆の判定まで証明。
  通常の指定 filtered 余錐の native な普遍性、path 座標を保つ交換同型、任意の strict Kan cospan の native な比較を証明。
  相対有限検出と全空間模型の元の余錐の native 余極限性を証明。小さい底上の一般 coherent 図式の HasColimit を公開。
  元の積比較の弱同値性・ホモトピー逆を証明。定値底の有限関手比較は cofinal、各値の内部 Hom 表示と path 比較を構成。
  始点評価の底上の逆と両端固定の Kan path 比較のホモトピー逆、二入力・単位上の全 path を保つ Kan 引き戻し比較を構成。
  形状制限の相対内部 Hom による底変換、元の両端評価と二入力射・引き戻し底射の left fibration 性を証明。
  各 fiber と元の三値の path 引き戻しの厳密な同型、三座標を保つ包含と元の値による相対有限検出を証明。
  任意の有限標的射を元の一値で検出し、元の Kan 比較への有限持ち上げと有限写像空間の π₀ の全射性を証明。
  全相対境界の単射有限近似、模型本体までの同時輸送と元の値への反映を構成。反映後の境界は厳密に保持。
  中央の全境界円柱を保持する相対 zigzag 合成を証明。
  共通境界付きの二入力の同時検出と相対還元を構成。任意の有限標的射を元の一値の実際の比較像で相対検出。
  任意の Kan 始域境界への相対持ち上げと、その境界を厳密に固定する補正を構成。
  全標準境界の path 置換終点の自明 Kan 性から、元の比較の弱同値性と単体的ホモトピー逆を証明。
  元の引き戻し全空間を native 極限錐の頂点に構成し、全錐の可逆比較・元の比較の頂点辺・恒等図式辺・各脚の自然性を保持。
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。
  a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合まで完了。
  a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全単体の交換、
  形状接着の錐空間の native 極限性、finiteShape_cell_induction を整備済み。
  coherentColimitFunctor は元の全空間頂点・native 余錐を保ち、指定各点余錐による完成と全錐の像を比較。
  元の単位三角柱の三三単体・共有面・上下二面・六側面と、全係数 EF⊗K の実 pointed 持ち上げを保持。
  元の指定三角形比較の二辺・長辺を同じ普遍 prism へ厳密に回収し、全 prism 比較の指定自然性を証明。
  元の相対三角形比較の前合成を、同じ全実三角形の三辺の指定比較で値まで同定。
  六共有辺の実 prism・実始点・実終点・指定比較を保ち、四面を同じ共通四頂点と六比較へ正規化。
  CoherentColimitUnitTetrahedronBoundary.comparison_square は同じ全族の四面の厳密な可換性。
  二内部三角形は元の三単体の実共有面そのもの。元の定値余極限三角形・外側六面を保持して境界を構成。
  三つの coherentColimitUnit{First,Middle,Last}TotalRelation は同じ元の全空間・恒等初期値上の指定関係。
  coherentColimitUnitTriangleValue_coherence は二内部面を消去した元の上下二面・指定対角の整合式。
  元の五因子全式を同じ固定 native 値へ写し、実三頂点・元の模型三角形を保って a6 の区間比較式へ代入済み。
  模型三角形式の下側輸送・上側単位を消去。残りの像を同じ raw fiber 二面比較の最後辺輸送で回収し、最初辺の元の模型比較への同じ射影と反映判定を証明。
  第一辺の模型比較への反映・最後辺輸送と四因子境界式は構成済み。全反転 Hom の pointed 族と元の raw 普遍三角形の始点固定比較を構成。
  pointedHomTriangleLongEvaluationComparison_eq_morphism / CompositeEvaluationComparison_eq_morphism は元の長辺・二辺評価比較を同じ固定射の比較へ同定。spaceCompositionZero_morphism_coherence は元の指定零面・精密化・値と三射の固定比較の整合式。元の全実長辺と固定射の実 prism は PointedMorphismPrismEquality / CoherentColimitApexLongMorphismPrism で一致。NativeComparison.postcomp V₂ と固定射の元の ValueComparison は CoherentColimitApexLongFixedValue で値まで一致。RawLongValueIso.precomp q の canonical 表示と移送初期係数の標準表示は CoherentColimitApexRawLongCanonical。coherentColimitApexLongRawValueRatio_heq_evaluation は同じ raw 値比較の逆と指定普遍比較の値の合成を元の右評価成分へ回収。coherentColimitApexLongRawValueRatio_cancel は raw 値比較と同じ比の合成を元の指定普遍比較へ厳密に回収。coherentColimitApexLongValueComposite_trans_ratio は元の LongComparison と raw 長辺値比較の合成に同じ比を続けると元の NativeComparison の値になることを証明。三つの実頂点の値を CoherentColimitApexLongValueVertices で照合し、coherentColimitApexLongEvaluationComparison_heq_value_composite は元の全三角形の長辺評価比較 Nlong を同じ実長辺比較と raw 長辺値比較の合成へ値まで同定（元の実結合表示は functorIsoOfEq で保持）。長辺評価の因子式は完了。relativePrismSpecified_naturality は始点も動く二実 prism の元の指定対角比較に対する可換正方形。全相対関手 R 上の同じ実評価 prism を比較・curry して構成し、一点成分は relativePrismDiagonalComparison_at_vertex で元の指定値へ回収。relativePrismActualEndpointIso_restrict_heq は辺制限後の実終点像と同じ全図式の終点評価の指定像の一致。relativePrismNativeEndpointIso_heq_initial_postcomp は固定区間の native 終点像を同じ実始点比較の同じ普遍輸送による後合成へ値まで同定。relativePrismEndpointImage_restrict_heq は同じ辺の両端像を元の全端点評価へ回収し、実始点表示は relativePrismInitialEndpointIso_restrict_heq。CoherentColimitApexPointedLastPrism は元の全初点係数を保つ最後辺の実始点・終点・底を保持し、projection_constant は底を元の raw 区間頂点の定値族へ厳密に同定。coherentColimitApexPointedLastConstantIso は元の PointedLastIso と値まで同じ固定区間上の比較。coherentColimitApexLastSpecified_naturality は元の最後辺の二実 prism・実両端・同じ指定比較の自然性正方形。coherentColimitApexLastNative_heq_initial_postcomp はその同じ native 像を実始点比較の普遍輸送による後合成へ同定。coherentColimitApexLastInitialEndpointIso_eq_middle / coherentColimitApexLastActualEndpointIso_eq_target はその実始点・終点像を元の全三角形の中間・終点比較へ厳密に同定。coherentColimitApexLastSpecified_endpoint_square / coherentColimitApexLastNative_heq_middle_postcomp は同じ正方形をその元の二比較で表示。spaceCompositionZeroFamily_last_eq_original は零面の実最後辺と元の最後辺の一致、middle/target_eq_original は同じ共有辺の両端作用の一致。spaceCompositionZeroFamily_first_eq_standard は退化した実初辺の一致。spaceCompositionZeroMiddleEndpointIso_eq_refl は同じ指定中間像の恒等性。relativePrismNativeEndpointIso_heq_initial_action / eq_refl_of_initial は全区間族の native 作用の始点評価への因数分解と恒等性の移送。未完：これらを零面の同じ最後辺制限比較に適用し、Ncomp の零面・終点比較・二 raw 辺値比較との値照合、spaceCompositionZero_morphism_coherence への二式の代入と零面値の消去による長辺値式、全錐比較と保存性。
  未完：同じ長辺輸送の残りと raw 二面比較の像の全区間族への照合・反映、二三角形・指定 path の全錐比較、引き戻し保存、
  部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。
  F1b は a7 のみ担当。完了時は F1 の交換入力に合う定理を公開し、次の割り当てを待つ。
- 残り：F1b は F2N-1 a7 のみ。F2N-3 は N、F2N-5 は F1。
- 依存：N の HomotopyLimits と F1 の straightening・前層・Yoneda は読み取り専用。
  F1 計画では前層・Yoneda は後続工程。提供済みの範囲をソースで確認し、存在を仮定して済ませない。
  N の一般の coherent 図式の余極限・γ4 の最新状況は e-infinity-algebras.md を参照。
  移管前の詳細は [archive/infinity-core-F2-N-handoff-2026-10-20.md](../../infinity-core-F2-N-handoff-2026-10-20.md)。
- 提供：F1 の IndFiniteLimitExchangeInput.exchange と同じ仮定・結論の全有限形状の交換定理。compact は N、Ind の安定性は F1。
- 所有：F2/ のトップレベルのみ。Ind/・Ind.lean（F1）、Compact/・Compact.lean と Idempotent/・Idempotent.lean（N）は読み取り専用。F2 集約・監査と両計画も所有。
- 既知の問題：通常の小圏の strict 図式だけでは一般の filtered 図式を網羅しない。
  Ind の生成・普遍性、冪等完備化の普遍性は構造の仮定にせず証明する。
- 次の一手：F2N-1 a7：ApexRawTriangleCandidate_eq_universal_iff の右辺（元の普遍比較の値＝同じ四因子境界式）を証明する。
  coherentColimitApexCoefficientMap は全反転 Hom から元の実初点 fiber への同値で包含を保持。
  coherentColimitApexPointedFamilyComparisonIso は元の raw 普遍三角形と spaceSimplexPointedFamily を同じ図式・初点を固定して比較する。
  PointedFirst/Last/LongIso は三面を元の実 prism に同定済み。RestrictionIso_precomp/shared と initial は二段制限・共有制限・初点の整合。
  三頂点の作用は SpaceTrianglePointedVertexActions で計算済み。Middle/TargetCoefficientMap は元の実 fiber 内の同じ全係数作用。
  PointedMiddle/TargetEndpointIso は同じ全比較の終点像。PointedLongTransport は δ₁ ▷ A ≫ spaceSimplexPointedFamily s と同じ実両端を持つ元の長区間の輸送証人。
  次の値照合は RawTriangleCandidate_eq_universal_iff_long_value の右辺：TargetEndpointIso.postcomp V₂ ≪≫ RawTriangleBoundaryAt B T q = PointedLongComparison.postcomp V₂。Nlong は coherentColimitApexLongEvaluationComparison_heq_value_composite で完了。Ncomp の零面値 ≪≫ PointedTargetEndpointIso.postcomp V₂ ≪≫ 二辺評価（元の RawLastValueIso・RawFirstValueIso の二因子）は未完。零面の元の指定中間像 spaceCompositionZeroMiddleEndpointIso_eq_refl は完成。具体的に M=coherentSimplexMaximalization s、A=元の全初点係数、r=δ₀▷A、β=r≫(fst Δ[2] A≫Yoneda M)、W=r≫family M、W′=r≫ZeroFamily、e=spaceCompositionTetrahedronZeroRestrictionIso s r と置く。始点の添字式 endpoint₀≫r=simplexPrismVertex 2 1 A と spaceCompositionZeroMiddleMap_standard/zero、spaceCompositionZeroMiddle_base で両実始点と底を揃える。spaceSimplexPointedRestrictionEndpointImage_heq_endpoint の i=0 と vertexIsoOfEq_heq により relativePrismInitialEndpointIso e を同じ spaceCompositionZeroMiddleEndpointIso s に厳密同定する。終点の底は SpaceCompositionZeroEndpointAction の spaceCompositionZeroEndpoint_base。relativePrismNativeEndpointIso_eq_refl_of_initial を適用し、同じ e の native 像を恒等にする。relativePrismSpecified_naturality の正方形から零面の実終点像 ≪≫ 元の最後辺の指定対角比較 = 最大化側の最後辺の指定対角比較を得る。W′ は spaceCompositionZeroFamily_last_eq_original で元の実最後辺に厳密一致。終点像は同じ汎用制限端点補題を i=1 で用いて元の零面値へ接続する。Apex 側の実最後辺の指定正方形は coherentColimitApexLastSpecified_endpoint_square、native 中間像は coherentColimitApexLastNative_heq_middle_postcomp で完成済み。coherent 合成四角形、pointedValueFamilyTransportIso_at_right と元の単位・余単位三角式で最大化側の比較を同じ二辺評価へ戻し、最後辺の raw 値比較を functorIso_whisker_exchange で同じ中間比較に沿って移す。元の RawLastValueIso・RawFirstValueIso を保持し Ncomp を独立に証明する。Nlong/Ncomp を spaceCompositionZero_morphism_coherence に代入し同じ零面値を消去、目標の長辺値式へ戻す。全零面・δ₀ 面の係数は元の s.obj 0。TargetEndpointIso_trans_universal や反映判定を未証明の値式の代用にしない。raw な全 ΦZero の中間像を直接 HEq の型に展開する補題は200k whnfに達したため採用せず、同じ値を保つ正規化端点と汎用制限補題を使う。資源上限は変更なし。
  δ₀ の面の係数は元の s.obj 0 のまま保持する。RawUniversalBoundary_iff_coefficient と of_long_value は、値照合から恒等初期値と任意の全初期値への忠実な反映を証明済み。反映を未証明の値式の代わりに使わない。
  RawUnitFiberComparison_eq_iff_model は元の最初辺模型比較への同じ射影で raw 比較を反映する。未完：長辺輸送の残りとの合成を同じ全族の三辺・指定三角形へ戻す。
  同じ余錐 fiber 写像の前合成の充満忠実性で整合を反映し、二三角形・指定 path を保つ全錐比較を束ねる。
  その極限性から引き戻し保存へ接続。値の整合式・辺ごとの同型だけでは全錐比較の完了としない。
  続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction。
  HTT §5.3.3、a7 残り12〜24時間（暫定。三角形に沿う全指定因子の照合に不確実性）。strict 図式だけでは完了としない。
  a7 後は全有限 K の CoherentFilteredLimitExchangeShape K を公開し、F1 の IndFiniteLimitExchangeInput.exchange に渡せることを確認して報告、次の割り当てを待つ。

| 工程 | 担当 | 内容と受入条件 | 原典 | 見積もり |
| --- | --- | --- | --- | --- |
| F2N-1 | F1b | filtered ∞ 圏と κ-filtered の定義、cofinality、𝒮 の filtered 余極限と有限極限の交換。一般の coherent な図式で証明する | HTT §5.3.1–3 | 40〜100 時間 |
| F2N-2 | F1（10-22 12:35 移管） | 前層の全部分 ∞ 圏として Indκ(C) を構成。filtered 余極限による生成と、保存関手の延長の普遍性を証明する | HTT 5.3.5.1–10 | 50〜120 時間 |
| F2N-3 | N | κ-compact、Yoneda 像の compact 性、retract による閉性、Ind の compact 対象の比較 | HTT §5.3.4、5.3.5.5・11 | 30〜80 時間 |
| F2N-4 | N | coherent な冪等図式と分裂、前層内の retract 閉包、冪等完備化の普遍性、compact 部分との同定 | HTT §5.1.4、5.3.4.17 | 40〜100 時間 |
| F2N-5 | F1 | C が小安定なら Ind(C) は安定。有限図式の filtered 表示と極限余極限の交換から証明し、冪等完備 C の compact 生成を公開 | HTT 5.3.3・5.3.5.15、HA §1.1.3 | 40〜100 時間 |

宇宙は第 1 部と共通。κ の正則性・図式の小ささを明示し、Indω と非連結 K 用の大きい κ を混同しない。
有限図式を C 内の図式の filtered 余極限で表示する際は、HTT 5.3.5.15 の有限半順序集合という条件を保持する。
presentable の一般論・随伴関手定理は F1b、Bousfield 局所化・P_Σ は N が I-b で分担する。
原典：[HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf) §5.1.4・§5.3。

## 4. F2 後半（本レーンの担当外）

| 工程 | 内容と受入条件 | 原典 |
| --- | --- | --- |
| F2P-1 | accessible ∞ 圏・accessible 関手、κ-compact 生成の濃度変更と Ind の比較 | HTT §5.4 |
| F2P-2 | presentable ∞ 圏の構成と特徴づけ、小余極限と accessible 局所化の接続 | HTT §5.5.1 |
| F2P-3 | presentable 間の随伴関手定理、余極限保存と左随伴、accessible な極限保存と右随伴の判定 | HTT §5.5.2 |

Bousfield 局所化・P_Σ は N の分担。上表の定理の結論を構造のフィールドに仮定しない。
実施記録はコミットメッセージ。本書には現在地と設計を置き、長い型一覧を追記しない。
