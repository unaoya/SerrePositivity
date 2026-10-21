# F2：F2-lite と presentable ∞ 圏（v2、F1b）

作成日：2026-10-18。更新日：2026-10-21。
正本は [foundations.md](foundations.md)。本書は F2-lite と F2 後半の正本。
F1b の前提工程は [infinity-core-F1b.md](infinity-core-F1b.md)、
N の γ3・γ4 は [e-infinity-algebras.md](e-infinity-algebras.md) を参照する。

## 引き継ぎ（2026-10-21）

### 現在地

- 第 1 部（B4・B5、F2L-1〜4）は完了。coherent nerve の Cat_∞、引き戻しと lax pullback、
  写像空間の普遍性、同値矢印の全部分圏との比較、安定性と完全な両射影まで証明済み。
- 10-20：F2N-1〜5（旧 N）を F1b へ移管。§3 が第 2 部の正本。
  κ-small/filtered の定義・ℵ₀ 比較、正則 κ の κ-small join と coslice の κ-filtered 性を証明。
  有限部分複体の filtered 表示を構成し、全ホーン付加の具体的な可算反復 Q を構成。
  Q の通常の filtered 余極限保存、全ての値の Kan 性、有限境界の元の有限部分複体への因子分解を証明。
  Q の単位の anodyne 性・弱同値性、一般の filtered ∞ 圏と有限図式の coslice の弱可縮性を証明。
  有限図式の coslice の頂点射影は right cofinal。標準 comma を図式の和の coslice と厳密に比較。
  対角関手の標準 comma を太い coslice と比較し、有限形状・正則 κ の小さい形状について
  filtered 性 ↔ coslice の弱可縮性 ↔ 対角関手の right cofinality を双方向に証明。
  filtered・κ-filtered 性のホモトピー retract 保存・同値不変性も証明。κ の正則性は輸送に不要。
  通常の filtered 図式では、有限内部 Hom の連続性、Kan 性・Kan fibration・自明 Kan fibration・
  任意の値の成分ごとの弱同値の保存、有限ホモトピーの段での相対検出を証明。
  Bousfield–Kan coend の重み・添字変更と合成則、Over.map に沿う図式と元の coend の表示同型を構成。
  通常・反転の両重みで、任意の値の通常の filtered 図式の標準 augmentation の弱同値性を証明。
  N の Kan coend から通常の Kan colimit へ実際の比較同値を構成し、augmentation との厳密な一致を証明。
  反転 augmentation の前合成を元の余錐の reflectedRepresentableComparison と全単体で同定。
  通常の指定余錐自体の native な普遍性を証明し、filteredKanColimitCocone もこの標準余錐へ揃えた。
  単体集合の filtered 余極限の有限極限保存を証明。Fun(Δ¹,−) の交換は両端評価を保つ。
  path 置換と二段の path 引き戻しの余極限の標準同型を構成し、元の二入力・全 path 座標への射影を保持。
  定値 path の切断の指定円柱に沿って全錐を輸送し、任意の二射の元の cospan の native な極限錐を構成。
  任意の strict Kan cospan 図式で、fibration 仮定なしの native な両普遍性と比較辺の可逆性を証明。
  一般 coherent filtered 図式の有限射・境界を元の一値で検出。底・部分図式の全円柱を保つ相対輸送も証明。
  有限ホモトピーと境界の充填を同じ fiber 内で検出。全値が可縮なら全空間模型も可縮。
  定値標的への変換と全空間からの写像空間の同値を構成。実際の単位から native 余錐を構成し、頂点を同定。
  native 余錐空間から定値変換空間への標準比較の厳密な左逆・ホモトピー右逆と同値性を証明。
  全空間内部 Hom 比較と両端固定の Kan path 比較は同値。Kan 引き戻し比較は二入力・単位上の全 path と厳密に一致。
  実現の両端固定ホモトピーを元の変換へ戻し、native 全空間余錐の比較の像と元の単位の同型を構成。
  元の全 Hom 三角形と相対合成を比較。定値 fiber の普遍輸送作用も同値で、全 Hom 比較を fiber 写像の前合成と比較。
  元の小さい単位の前合成同値を厳密な宇宙移送で必要な全 fiber 標的へ戻し、構成済み余錐の native 余極限性を証明。
  小さい底上の任意の coherent 空間値図式の HasColimit を公開。filtered 性・strict 図式への置換は不要。
  共通境界付き同時検出を構成。対角の cofinality の底変換から、元の全空間 Kan 積比較の弱同値性・ホモトピー逆を証明。
  定値底の形状制限は相対内部 Hom の底変換。両端評価と path 引き戻しの二入力射・底射の left fibration 性を証明。
  各 fiber と元の三値の path 引き戻しの厳密な同型、三座標を保つ包含、元の値による境界固定の相対有限検出を証明。
  全境界正方形と端点固定反映を元の比較へ合成。任意の有限標的射を、元の一値の実際の引き戻し比較像で検出。
  有限持ち上げと有限写像空間の π₀ の全射性を証明。全相対境界を保つ模型本体の同時輸送と元の値への反映を構成。反映後の射は元の境界値と厳密に一致。
  一般 Kan 標的で相対ホーン充填、境界定値な反転と左右の合成、中央の全境界円柱を保つ三比較の zigzag 合成を証明。
  任意の有限標的射の二入力を、共通の元の境界円柱を保って元の fiber へ同時に輸送・反映し、実際の比較射への相対有限検出・持ち上げを構成。値の射の境界と全比較円柱の制限を厳密に保持。
  任意の Kan 境界で相対持ち上げを構成し、境界移動を除去。元の全空間 Kan 引き戻し比較の弱同値性・ホモトピー逆を全標準境界の path 置換充填から証明。
  元の引き戻し全空間を native 極限錐の頂点に構成。元の比較の頂点辺・恒等図式辺を持つ全錐比較と各脚の h での自然性を保持。
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合、coherentCospanConeNativeComparison_isWeakHomotopyEquivalence まで完了。a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全標準単体の交換、形状の接着の錐空間の native 極限性を証明。finiteShape_cell_induction と CoherentFilteredLimitExchangeShape、空形状・単体の極限の存在を整備。部分極限の coherent な錐族と底を固定する比較三角形、元の全関手 cospan 錐の二三角形を保つ coherent 表示と各点の a6 への適用を構成。coherentColimitFunctor は全小 coherent 図式の元の全空間頂点と native 余錐を厳密に保ち、coherentCompletedLimit_iff_colimitFunctor は元の任意の指定点ごとの余錐による完成を全錐の像へ比較。元の単位正方形の上下三角形から輸送の同型を反映し、coherentColimitIntervalNativeHomotopy は指定辺と native 区間表示の両端固定全円柱を保持。coherentColimitTransportValueIso は元の具体的 Kan 頂点射との輸送の値の比較。coherentColimitEdgeValueNativeIso は同じ全円柱の上下二単体から Kan 値の射の比較を構成し、kanFixedSquareUpperIso_heq・kanFixedSquareLowerIso_heq は元の精密化同型を保持。coherentColimitEdgeValueIso は元の余極限辺の Kan 値を、同じ始域の表示変更を保って a6 の coherentTotalMapNativeValueDown と直接比較。HomotopyLimits.pointedValue_transportIso を読み取り専用で再利用し、選択済み値比較を保持。pointedValueFamilyTransportIso は同じパラメータで動く点と Kan 射の全族へ比較を拡張し、元の単位・余単位を保持。pointedValueHomActionIso は全 Hom 空間上の比較、pointedValueTriangleEvaluationEdge_hom は元の指定三角形同型の持ち上げと前合成を回収。pointedValueTriangle_isoSquare は同じ精密化辺の輸送と両端比較の同型の整合式。coherentColimitApexTriangle_isoSquare は元の余極限二単体の三辺を厳密に回収して適用。coherentColimitUnitCospanHomotopy は元の全錐から余極限像の定値図式への単位全円柱。左右の単位三角柱、三三単体の共有面・上下二面・六側面を元の上下単位三角形へ厳密に同定。RelativeExtensionEndpointWitness.iso_trans は既存の指定終点比較の合成則。元の三三単体の全底・共通始点 F を保つ pointed 持ち上げと可縮な選択空間、その実際の頂点を構成。同じ零頂点を含む面は coherentColimitUnitPointedFaceIso で元の指定二単体の選択空間へ底と初期値を揃え、元の実延長・指定比較・その合成を保持。元の全三単体の普遍的 pointed 持ち上げを構成。第零面は初期値を動かす coherentColimitUnitPointedZeroFaceFamily とし、全延長空間の可縮性・元の実制限による切断・指定比較の一致を証明。中央・最後の第一辺を元の指定第一変換へ同定。coherentColimitUnitPointedFirstEdgeWitness と coherentColimitUnitPointedFirstEdgeComparison は実第一辺と実終点を元の変換族の証拠・既存の指定始域比較へ全選択で接続。functorTrianglePointedLift は元の指定三角形比較の同じ持ち上げを全底へ戻し、底・初期値・長辺を保持。coherentColimitUnitMiddleZeroFaceComparison・coherentColimitUnitLastZeroFaceComparison は元の第零面と、実第一辺の終点で前合成した元の上下単位三角形の同じ全パラメータ固定の比較。functorTrianglePointedLift_comparison_pre は元の相対三角形比較を同じ長辺証拠の指定終点比較へ値まで戻す。functorTrianglePointedLift_target は元の指定三角形の終点を、元の二つの選択済み全空間作用の厳密な合成へ同定。第零面の元の実終点は元の全三単体の同じ最終頂点の制限。coherentColimitUnitZeroFaceEndpointIso_heq_map は、構成済み全族比較の終点像を同じ native 合成比較へ値まで同定。coherentColimitUnitZeroFaceEdgeComparison は同じ全族比較の三辺への像で、長辺の標的も元の指定比較の同じ長辺証拠と一致。coherentColimitUnitZeroFaceEndpointIso_heq_edge は長辺・最後の辺の指定比較が、終点で同じ native 合成比較に一致することを保持。pointedTriangleFamilyLongRestriction は全族を結合子で同じ全係数の長辺選択空間へ移し、元の比較・実証拠・終点評価を保持。元の普遍長辺・実長辺・指定三角形の長辺を同じ証拠型へ束ね、coherentColimitUnitZeroFaceLongIso_trans で指定比較の合成を証明。coherentColimitUnitZeroFaceLongTriangleIso_eq_native は中間比較を構成済みの native 終点比較へ厳密に同定。底・全初期値・終点底の厳密な表示変更を元の実延長・実終点のまま行い、coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite は元の指定三角形比較の実第一辺での前合成を、同じ長辺の指定始域比較と native 終点比較の合成へ値まで同定。functorHomotopySourceEndpointIso_heq_component は元の実 prism の指定比較を、全係数を保った F1 の全族比較の同じ成分へ同定。coherentColimitUnitZeroFaceLongSourceIso_heq_component で第零面の LongSourceIso に適用済み。固定始点の面も coherentColimitUnitPointedFixedFaceOriginalComparison で元の実二面と元の指定三角形の同じ持ち上げを全選択・全初期値固定の空間で比較。三辺への制限・元の長辺証拠の回収・全実終点の native 合成比較と全族比較の終点像との一致を証明。coherentColimitUnitPointedFixedFaceLongSource_native_trans は長辺三証拠の同じ指定比較の合成式。coherentColimitUnitPointedFixedFaceSpecifiedTriangle_pre_heq_composite は元の指定三角形比較の全空間射影での前合成を同じ指定始域比較と native 終点比較の合成へ値まで同定。coherentColimitUnitPointedFixedFaceLongSourceIso_heq_component は同じ始域比較を F1 の全族比較の指定成分へ同定。coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace は最終頂点を含む固定面と第零面の元の実終点を全選択上で厳密に同定。coherentColimitUnitLastEndpoints_eq で最後の三単体の元の二つの上単位側面へ適用。固定面の長辺・最後の辺の終点像は同じ元の native 終点比較へ一致。始点も動く全相対 prism 空間で、functorHomotopyPrismSection の始点評価は恒等、終点評価は元の native 作用の後合成に厳密に一致。functorHomotopyPrismEndpointComparison_naturality は全 prism 比較の指定自然性。始点評価の充満忠実性と初期値固定の全延長族の始点での定値性から、functorHomotopyPrismEndpointComparison_heq_specified・functorHomotopyPrismEndpointComparison_heq_F1_component で各点を元の指定比較・F1 全族比較の同じ成分へ値まで同定。functorTrianglePointedLift_first・second は元の指定三角形の二辺を元の二つの普遍 prism の実制限へ厳密に回収。functorTriangleCanonical_second_sourceIso_heq_refl は元の指定右辺の比較の恒等性。FunctorTrianglePointedWitness は元の全実三角形と三つの実辺証拠を保持し、right_specified_naturality で同じ全族の右辺比較に指定自然性を適用。rightActualComparison_eq_endpoint は右辺の終点像を同じ全三角形比較の終点像へ厳密に同定。rightNativeComparison_eq は canonical 右辺の恒等性を使い、終点比較を元の第二始域比較と右辺の始点像の native 作用へ結ぶ。coherentColimitUnitZeroFaceTriangleWitness・coherentColimitUnitPointedFixedFaceTriangleWitness は元の単位三単体の全持ち上げを EF⊗K を保ったまま同じ証拠型へ接続。未完：これらの指定比較の元の二三角形・指定 path との整合、全錐比較と余極限関手の引き戻し保存、部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。その後 Ind・compact・冪等完備化・安定性・compact 生成、presentable・随伴関手定理。
  三集約同時ビルド9362 jobs、公理監査10954宣言・F1/F1B 同時 import 成功、標準三公理のみ。元の指定三角形の二辺の実制限、右辺への指定自然性と全終点像・恒等比較の簡約、元の零面・固定面の全実持ち上げへの接続の追加63明示宣言も型検査。追加 ModelCategory 仮定・ソースの名前衝突なし。

### 残り（依存順、実作業時間の概算）

- F2N-1：𝒮 の一般 coherent filtered 余極限と有限極限との交換。全空間模型の native 余極限性は証明済み。
- F2N-2：前層内の Indκ、生成と保存関手の延長の普遍性。50〜120 時間。
- F2N-3・4：compact・retract、coherent 冪等図式と完備化の普遍性。各 30〜100 時間。
- F2N-5：Ind(C) の安定性、冪等完備 C の compact 生成。40〜100 時間。
- その後 F2 後半：presentable と随伴関手定理（F1b）。HTT §5.5、Kerodon 9。細分化は §4。
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

### 依存と提供

- N の HomotopyLimits（γ3c の 𝒮 の余極限）と F1 の straightening は読み取り専用。
  γ4 は前提として一括仮定せず、必要な公開界面と提供済みの範囲を確認する。
- D の β4 と K-基盤へ第 1 部の界面を提供。第 2 部の Ind・compact・冪等完備化は F1b が提供する。

### 未コミット

- 所有パスの未コミットなし（本保存後）。移管前の N の記載は archive に保持。

### 既知の問題

- F1 の前層・Yoneda は F1 計画の後続工程。Ind の存在を仮定して回避しない。前回 F1 の QuasicategoryEnrichedDiagramRealization のエラーは、今回の三集約同時ビルド・同時 import で解消を確認。
- 一般の coherent な図式の余極限と、通常の小圏による strict 図式の余極限を区別する。
- 既存 anodyneKanObject の保存性を仮定せず、連続な Q と単位の anodyne 性・弱同値性を具体的に証明。
  通常の指定余錐の全脚・高次の整合性を保持した native な普遍性まで証明済み。
  任意の二射の元の cospan の native な極限との比較は証明済み。一般 coherent filtered 図式の交換は残る。
  全空間模型の余錐全体・頂点・単位との比較は構成済み。余錐空間の比較同値と元の単位との同型は証明済み。
  元の全空間余錐への全 Hom 判定の適用は完了。必要な fiber 標的を明示し、小さい単位の比較から証明。
- 主経路に追加公理・sorry・ModelCategory SSet の instance 仮定を置かない。

### 次の一手

- F2N-1 a7：元の任意の指定余錐による完成を coherentColimitFunctor の全錐の像へ比較済み。coherentColimitEdgeValueIso は元の余極限指定辺の Kan 値を、同じ始域表示を保って a6 の coherentTotalMapNativeValueDown と直接比較。pointedValueTriangle_isoSquare は全 Hom 比較の自然性から、元の指定三角形同型の持ち上げ・前合成と同じ精密化辺の輸送を、指定両端比較で結ぶ。元の余極限二単体への適用は coherentColimitApexTriangle_isoSquare、全錐の単位円柱は coherentColimitUnitCospanHomotopy。三単体の共有面・上下二面・六側面を元の上下単位三角形へ同定済み。元の三三単体の pointed 持ち上げ・全底と初期値を固定する可縮な選択空間・同じ零頂点の二面への実際の制限と指定比較の合成は証明済み。底・初期値の正規化は coherentColimitUnitPointedFaceIso、指定比較と合成の保存は coherentColimitUnitPointedFaceComparison_normalized_trans まで証明。第零面の可変初期値の全延長族・可縮性・元の実制限の切断を構成し、coherentColimitUnitPointedZeroFace_boundary_firstEdge は第一辺の終点との全パラメータの厳密な一致を保持。中央・最後の底も元の上下単位三角形へ同定済み。第一辺の実 prism は coherentColimitUnitPointedFirstEdgeWitness と既存の同じ指定始域比較へ接続済み。元の指定三角形比較の同じ全持ち上げ・長辺証拠・指定終点比較を functorTrianglePointedLift・functorTrianglePointedLift_long・functorTrianglePointedLift_comparison_pre で保持。coherentColimitUnitMiddleZeroFaceComparison・coherentColimitUnitLastZeroFaceComparison は、元の第零面と実第一辺の終点で前合成した元の上下単位三角形を全パラメータ固定の選択空間で比較する。三辺への指定比較の像・元の長辺証拠の回収・全終点の native 合成表示は証明済み。coherentColimitUnitZeroFaceEndpointIso_heq_edge は長辺・最後の辺の指定比較の終点を、同じ全族比較の元の native 終点比較へ値まで同定。結合子による長辺制限・三証拠の同じ指定終点比較の合成・中間比較の native 終点比較との厳密な一致を証明済み。coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite は「元の指定三角形比較の実第一辺での前合成＝長辺三証拠の指定始域比較≫構成済みの native 終点比較」を同じ元の指定値で保持。第零面と固定始点の面の両方で、元の指定三角形比較＝同じ長辺の指定始域比較≫native 終点比較、および指定始域比較＝F1 全族比較の同じ成分まで証明済み。最終頂点を含む固定面と第零面の実終点の厳密な一致は coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace、最後の元の二側面への適用は coherentColimitUnitLastEndpoints_eq まで完了。元の指定三角形の第一辺・右辺の同じ普遍 prism の実制限、canonical 右辺の指定比較の恒等性、同じ全三角形比較の右辺への指定自然性と全終点像との一致まで完了。FunctorTrianglePointedWitness.rightNativeComparison_eq は「右辺の始点像の native 作用＝元の第二始域比較≫同じ全三角形の終点比較」を元の指定値で保持。次は同じ全三角形の中間評価を構成し、右辺の始点評価＝第一辺の終点評価を厳密に同定する。右辺の native 始点比較を中間比較の後合成へ戻す。第一辺では全初期値が固定されるので、始点像の定値性と canonical 第一辺の恒等性から中間比較＝元の第一始域比較の逆を示す。これを rightNativeComparison_eq と合わせ、全終点比較を元の二辺の指定始域比較で表す。元の長辺三証拠の合成と functorTrianglePointedLift_comparison_pre へ接続し、元の指定三角形比較を同じ三辺の実 prism 比較から表示する。零面・固定面の元の全持ち上げへの接続は coherentColimitUnitZeroFaceTriangleWitness・coherentColimitUnitPointedFixedFaceTriangleWitness、旧全族比較との値の照合は結合子と底・初期値の表示変更を保って行う。元の同じ全三単体の各辺の比較から四面の式を一つの表示に揃え、三単体の三関係を得る。零面は coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite と coherentColimitUnitZeroFaceLongSourceIso_heq_component、固定面は coherentColimitUnitPointedFixedFaceSpecifiedTriangle_pre_heq_composite と coherentColimitUnitPointedFixedFaceLongSourceIso_heq_component を使う。全選択パラメータ EF⊗K と元の指定同型を保持。面ごとの式の照合だけでは三単体の三関係・全錐比較の完了としない。六面の指定比較の三関係から共有面を消去し、a6 の native 合成比較との整合式を示す。これを元の余極限二単体の値の正方形と結び、二三角形・指定 path を保つ native 全錐比較を束ねる。その全錐の極限性から引き戻し保存へ接続する。辺ごとの同型だけでは全錐比較を結論しない。続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction（HTT §5.3.3、残り12〜24時間、暫定・指定比較の照合に不確実性）。strict な通常図式だけでは完了としない。その後 F2N-2〜5、presentable・随伴関手定理。
  元の指定 path と境界の全円柱を保持し、有限写像空間の π₀ の全射性だけで弱同値性を結論しない。

## 0. 目標と範囲

| 工程 | 担当 | 到達点 | 原典 |
| --- | --- | --- | --- |
| F2L-1 | F1b | 完了：Cat_∞ の対象・辺・関手 core との写像空間比較、関手の同値の判定 | Kerodon §5.5.3 |
| F2L-2 | F1b | 完了：Cat_∞ の引き戻し、全試験写像空間の普遍性、二射影と指定 path の同時比較 | Kerodon §5.5.3、HTT §3.3.3 |
| F2L-3 | F1b | 完了：lax pullback、対象三つ組、native 極限錐、全試験関手 core、Remark 6 の写像空間の 𝒮 内の極限性 | Tamme §1 Definition 5・Remark 6 |
| F2L-4 | F1b（D と接続） | 完了：通常の引き戻しとの比較、安定性・完全な両射影、極限・余極限の成分判定 | Tamme §1 Remark 7・Lemma 8 |
| F2N-1〜5 | F1b（10-20 に N から移管） | filtered、Ind、compact、冪等完備化、Ind の安定性 | HTT §5.1.4・§5.3、Kerodon 9 |
| F2 後半 | F1b（presentable・随伴関手定理）／N（Bousfield・P_Σ） | presentable、随伴関手定理、Bousfield 局所化、P_Σ | HTT §5.5、Kerodon 9 |

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

## 3. F2-lite 第 2 部（F1b、旧 N から移管）

### 引き継ぎ（F1b、2026-10-20 移管）

- 現在地：F2N-1〜5 を旧 N から F1b へ移管。第 1 部の Cat_∞・lax pullback は完了済み。
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
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合、coherentCospanConeNativeComparison_isWeakHomotopyEquivalence まで完了。a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全標準単体の交換、形状の接着の錐空間の native 極限性を証明。finiteShape_cell_induction と CoherentFilteredLimitExchangeShape、空形状・単体の極限の存在を整備。部分極限の coherent な錐族と底を固定する比較三角形、元の全関手 cospan 錐の二三角形を保つ coherent 表示と各点の a6 への適用を構成。coherentColimitFunctor は全小 coherent 図式の元の全空間頂点と native 余錐を厳密に保ち、coherentCompletedLimit_iff_colimitFunctor は元の任意の指定点ごとの余錐による完成を全錐の像へ比較。元の単位正方形の上下三角形から輸送の同型を反映し、coherentColimitIntervalNativeHomotopy は指定辺と native 区間表示の両端固定全円柱を保持。coherentColimitTransportValueIso は元の具体的 Kan 頂点射との輸送の値の比較。coherentColimitEdgeValueNativeIso は同じ全円柱の上下二単体から Kan 値の射の比較を構成し、kanFixedSquareUpperIso_heq・kanFixedSquareLowerIso_heq は元の精密化同型を保持。coherentColimitEdgeValueIso は元の余極限辺の Kan 値を、同じ始域の表示変更を保って a6 の coherentTotalMapNativeValueDown と直接比較。HomotopyLimits.pointedValue_transportIso を読み取り専用で再利用し、選択済み値比較を保持。pointedValueFamilyTransportIso は同じパラメータで動く点と Kan 射の全族へ比較を拡張し、元の単位・余単位を保持。pointedValueHomActionIso は全 Hom 空間上の比較、pointedValueTriangleEvaluationEdge_hom は元の指定三角形同型の持ち上げと前合成を回収。pointedValueTriangle_isoSquare は同じ精密化辺の輸送と両端比較の同型の整合式。coherentColimitApexTriangle_isoSquare は元の余極限二単体の三辺を厳密に回収して適用。coherentColimitUnitCospanHomotopy は元の全錐から余極限像の定値図式への単位全円柱。左右の単位三角柱、三三単体の共有面・上下二面・六側面を元の上下単位三角形へ厳密に同定。RelativeExtensionEndpointWitness.iso_trans は既存の指定終点比較の合成則。元の三三単体の全底・共通始点 F を保つ pointed 持ち上げと可縮な選択空間、その実際の頂点を構成。同じ零頂点を含む面は coherentColimitUnitPointedFaceIso で元の指定二単体の選択空間へ底と初期値を揃え、元の実延長・指定比較・その合成を保持。元の全三単体の普遍的 pointed 持ち上げを構成。第零面は初期値を動かす coherentColimitUnitPointedZeroFaceFamily とし、全延長空間の可縮性・元の実制限による切断・指定比較の一致を証明。中央・最後の第一辺を元の指定第一変換へ同定。coherentColimitUnitPointedFirstEdgeWitness と coherentColimitUnitPointedFirstEdgeComparison は実第一辺と実終点を元の変換族の証拠・既存の指定始域比較へ全選択で接続。functorTrianglePointedLift は元の指定三角形比較の同じ持ち上げを全底へ戻し、底・初期値・長辺を保持。coherentColimitUnitMiddleZeroFaceComparison・coherentColimitUnitLastZeroFaceComparison は元の第零面と、実第一辺の終点で前合成した元の上下単位三角形の同じ全パラメータ固定の比較。functorTrianglePointedLift_comparison_pre は元の相対三角形比較を同じ長辺証拠の指定終点比較へ値まで戻す。functorTrianglePointedLift_target は元の指定三角形の終点を、元の二つの選択済み全空間作用の厳密な合成へ同定。第零面の元の実終点は元の全三単体の同じ最終頂点の制限。coherentColimitUnitZeroFaceEndpointIso_heq_map は、構成済み全族比較の終点像を同じ native 合成比較へ値まで同定。coherentColimitUnitZeroFaceEdgeComparison は同じ全族比較の三辺への像で、長辺の標的も元の指定比較の同じ長辺証拠と一致。coherentColimitUnitZeroFaceEndpointIso_heq_edge は長辺・最後の辺の指定比較が、終点で同じ native 合成比較に一致することを保持。pointedTriangleFamilyLongRestriction は全族を結合子で同じ全係数の長辺選択空間へ移し、元の比較・実証拠・終点評価を保持。元の普遍長辺・実長辺・指定三角形の長辺を同じ証拠型へ束ね、coherentColimitUnitZeroFaceLongIso_trans で指定比較の合成を証明。coherentColimitUnitZeroFaceLongTriangleIso_eq_native は中間比較を構成済みの native 終点比較へ厳密に同定。底・全初期値・終点底の厳密な表示変更を元の実延長・実終点のまま行い、coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite は元の指定三角形比較の実第一辺での前合成を、同じ長辺の指定始域比較と native 終点比較の合成へ値まで同定。functorHomotopySourceEndpointIso_heq_component は元の実 prism の指定比較を、全係数を保った F1 の全族比較の同じ成分へ同定。coherentColimitUnitZeroFaceLongSourceIso_heq_component で第零面の LongSourceIso に適用済み。固定始点の面も coherentColimitUnitPointedFixedFaceOriginalComparison で元の実二面と元の指定三角形の同じ持ち上げを全選択・全初期値固定の空間で比較。三辺への制限・元の長辺証拠の回収・全実終点の native 合成比較と全族比較の終点像との一致を証明。coherentColimitUnitPointedFixedFaceLongSource_native_trans は長辺三証拠の同じ指定比較の合成式。coherentColimitUnitPointedFixedFaceSpecifiedTriangle_pre_heq_composite は元の指定三角形比較の全空間射影での前合成を同じ指定始域比較と native 終点比較の合成へ値まで同定。coherentColimitUnitPointedFixedFaceLongSourceIso_heq_component は同じ始域比較を F1 の全族比較の指定成分へ同定。coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace は最終頂点を含む固定面と第零面の元の実終点を全選択上で厳密に同定。coherentColimitUnitLastEndpoints_eq で最後の三単体の元の二つの上単位側面へ適用。固定面の長辺・最後の辺の終点像は同じ元の native 終点比較へ一致。始点も動く全相対 prism 空間で、functorHomotopyPrismSection の始点評価は恒等、終点評価は元の native 作用の後合成に厳密に一致。functorHomotopyPrismEndpointComparison_naturality は全 prism 比較の指定自然性。始点評価の充満忠実性と初期値固定の全延長族の始点での定値性から、functorHomotopyPrismEndpointComparison_heq_specified・functorHomotopyPrismEndpointComparison_heq_F1_component で各点を元の指定比較・F1 全族比較の同じ成分へ値まで同定。functorTrianglePointedLift_first・second は元の指定三角形の二辺を元の二つの普遍 prism の実制限へ厳密に回収。functorTriangleCanonical_second_sourceIso_heq_refl は元の指定右辺の比較の恒等性。FunctorTrianglePointedWitness は元の全実三角形と三つの実辺証拠を保持し、right_specified_naturality で同じ全族の右辺比較に指定自然性を適用。rightActualComparison_eq_endpoint は右辺の終点像を同じ全三角形比較の終点像へ厳密に同定。rightNativeComparison_eq は canonical 右辺の恒等性を使い、終点比較を元の第二始域比較と右辺の始点像の native 作用へ結ぶ。coherentColimitUnitZeroFaceTriangleWitness・coherentColimitUnitPointedFixedFaceTriangleWitness は元の単位三単体の全持ち上げを EF⊗K を保ったまま同じ証拠型へ接続。未完：これらの指定比較の元の二三角形・指定 path との整合、全錐比較と余極限関手の引き戻し保存、部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。その後 Ind・compact・冪等完備化・安定性・compact 生成、presentable・随伴関手定理。
- 残り：F2N-1 → F2N-2 → F2N-3・4 → F2N-5（下表）。
- 依存：N の HomotopyLimits と F1 の straightening・前層・Yoneda は読み取り専用。
  F1 計画では前層・Yoneda は後続工程。提供済みの範囲をソースで確認し、存在を仮定して済ませない。
  N の一般の coherent 図式の余極限・γ4 の最新状況は e-infinity-algebras.md を参照。
  移管前の詳細は [archive/infinity-core-F2-N-handoff-2026-10-20.md](archive/infinity-core-F2-N-handoff-2026-10-20.md)。
- 提供：K-基盤へ Ind の κ 版・compact・冪等完備化、D へ安定性の界面。
- 所有：F2/、F2 集約・監査、本計画と F1b 計画。HomotopyLimits/ と F1/ は編集しない。
- 既知の問題：通常の小圏の strict 図式だけでは一般の filtered 図式を網羅しない。
  Ind の生成・普遍性、冪等完備化の普遍性は構造の仮定にせず証明する。
- 次の一手：F2N-1 a7：元の任意の指定余錐による完成を coherentColimitFunctor の全錐の像へ比較済み。coherentColimitEdgeValueIso は元の余極限指定辺の Kan 値を、同じ始域表示を保って a6 の coherentTotalMapNativeValueDown と直接比較。pointedValueTriangle_isoSquare は全 Hom 比較の自然性から、元の指定三角形同型の持ち上げ・前合成と同じ精密化辺の輸送を、指定両端比較で結ぶ。元の余極限二単体への適用は coherentColimitApexTriangle_isoSquare、全錐の単位円柱は coherentColimitUnitCospanHomotopy。三単体の共有面・上下二面・六側面を元の上下単位三角形へ同定済み。元の三三単体の pointed 持ち上げ・全底と初期値を固定する可縮な選択空間・同じ零頂点の二面への実際の制限と指定比較の合成は証明済み。底・初期値の正規化は coherentColimitUnitPointedFaceIso、指定比較と合成の保存は coherentColimitUnitPointedFaceComparison_normalized_trans まで証明。第零面の可変初期値の全延長族・可縮性・元の実制限の切断を構成し、coherentColimitUnitPointedZeroFace_boundary_firstEdge は第一辺の終点との全パラメータの厳密な一致を保持。中央・最後の底も元の上下単位三角形へ同定済み。第一辺の実 prism は coherentColimitUnitPointedFirstEdgeWitness と既存の同じ指定始域比較へ接続済み。元の指定三角形比較の同じ全持ち上げ・長辺証拠・指定終点比較を functorTrianglePointedLift・functorTrianglePointedLift_long・functorTrianglePointedLift_comparison_pre で保持。coherentColimitUnitMiddleZeroFaceComparison・coherentColimitUnitLastZeroFaceComparison は、元の第零面と実第一辺の終点で前合成した元の上下単位三角形を全パラメータ固定の選択空間で比較する。三辺への指定比較の像・元の長辺証拠の回収・全終点の native 合成表示は証明済み。coherentColimitUnitZeroFaceEndpointIso_heq_edge は長辺・最後の辺の指定比較の終点を、同じ全族比較の元の native 終点比較へ値まで同定。結合子による長辺制限・三証拠の同じ指定終点比較の合成・中間比較の native 終点比較との厳密な一致を証明済み。coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite は「元の指定三角形比較の実第一辺での前合成＝長辺三証拠の指定始域比較≫構成済みの native 終点比較」を同じ元の指定値で保持。第零面と固定始点の面の両方で、元の指定三角形比較＝同じ長辺の指定始域比較≫native 終点比較、および指定始域比較＝F1 全族比較の同じ成分まで証明済み。最終頂点を含む固定面と第零面の実終点の厳密な一致は coherentColimitUnitPointedFixedFaceEndpoint_eq_zeroFace、最後の元の二側面への適用は coherentColimitUnitLastEndpoints_eq まで完了。元の指定三角形の第一辺・右辺の同じ普遍 prism の実制限、canonical 右辺の指定比較の恒等性、同じ全三角形比較の右辺への指定自然性と全終点像との一致まで完了。FunctorTrianglePointedWitness.rightNativeComparison_eq は「右辺の始点像の native 作用＝元の第二始域比較≫同じ全三角形の終点比較」を元の指定値で保持。次は同じ全三角形の中間評価を構成し、右辺の始点評価＝第一辺の終点評価を厳密に同定する。右辺の native 始点比較を中間比較の後合成へ戻す。第一辺では全初期値が固定されるので、始点像の定値性と canonical 第一辺の恒等性から中間比較＝元の第一始域比較の逆を示す。これを rightNativeComparison_eq と合わせ、全終点比較を元の二辺の指定始域比較で表す。元の長辺三証拠の合成と functorTrianglePointedLift_comparison_pre へ接続し、元の指定三角形比較を同じ三辺の実 prism 比較から表示する。零面・固定面の元の全持ち上げへの接続は coherentColimitUnitZeroFaceTriangleWitness・coherentColimitUnitPointedFixedFaceTriangleWitness、旧全族比較との値の照合は結合子と底・初期値の表示変更を保って行う。元の同じ全三単体の各辺の比較から四面の式を一つの表示に揃え、三単体の三関係を得る。零面は coherentColimitUnitZeroFaceSpecifiedTriangle_pre_heq_composite と coherentColimitUnitZeroFaceLongSourceIso_heq_component、固定面は coherentColimitUnitPointedFixedFaceSpecifiedTriangle_pre_heq_composite と coherentColimitUnitPointedFixedFaceLongSourceIso_heq_component を使う。全選択パラメータ EF⊗K と元の指定同型を保持。面ごとの式の照合だけでは三単体の三関係・全錐比較の完了としない。六面の指定比較の三関係から共有面を消去し、a6 の native 合成比較との整合式を示す。これを元の余極限二単体の値の正方形と結び、二三角形・指定 path を保つ native 全錐比較を束ねる。その全錐の極限性から引き戻し保存へ接続する。辺ごとの同型だけでは全錐比較を結論しない。続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction（HTT §5.3.3、残り12〜24時間、暫定・指定比較の照合に不確実性）。strict な通常図式だけでは完了としない。その後 F2N-2〜5、presentable・随伴関手定理。

| 工程 | 担当 | 内容と受入条件 | 原典 | 見積もり |
| --- | --- | --- | --- | --- |
| F2N-1 | F1b | filtered ∞ 圏と κ-filtered の定義、cofinality、𝒮 の filtered 余極限と有限極限の交換。一般の coherent な図式で証明する | HTT §5.3.1–3 | 40〜100 時間 |
| F2N-2 | F1b | 前層の全部分 ∞ 圏として Indκ(C) を構成。filtered 余極限による生成と、保存関手の延長の普遍性を証明する | HTT 5.3.5.1–10 | 50〜120 時間 |
| F2N-3 | F1b | κ-compact、Yoneda 像の compact 性、retract による閉性、Ind の compact 対象の比較 | HTT §5.3.4、5.3.5.5・11 | 30〜80 時間 |
| F2N-4 | F1b | coherent な冪等図式と分裂、前層内の retract 閉包、冪等完備化の普遍性、compact 部分との同定 | HTT §5.1.4、5.3.4.17 | 40〜100 時間 |
| F2N-5 | F1b | C が小安定なら Ind(C) は安定。有限図式の filtered 表示と極限余極限の交換から証明し、冪等完備 C の compact 生成を公開 | HTT 5.3.3・5.3.5.15、HA §1.1.3 | 40〜100 時間 |

宇宙は第 1 部と共通。κ の正則性・図式の小ささを明示し、Indω と非連結 K 用の大きい κ を混同しない。
有限図式を C 内の図式の filtered 余極限で表示する際は、HTT 5.3.5.15 の有限半順序集合という条件を保持する。
presentable の一般論・随伴関手定理は F1b、Bousfield 局所化・P_Σ は N が I-b で分担する。
原典：[HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf) §5.1.4・§5.3。

## 4. F2 後半（第 2 部の後、F1b）

| 工程 | 内容と受入条件 | 原典 |
| --- | --- | --- |
| F2P-1 | accessible ∞ 圏・accessible 関手、κ-compact 生成の濃度変更と Ind の比較 | HTT §5.4 |
| F2P-2 | presentable ∞ 圏の構成と特徴づけ、小余極限と accessible 局所化の接続 | HTT §5.5.1 |
| F2P-3 | presentable 間の随伴関手定理、余極限保存と左随伴、accessible な極限保存と右随伴の判定 | HTT §5.5.2 |

Bousfield 局所化・P_Σ は N の分担。上表の定理の結論を構造のフィールドに仮定しない。
実施記録はコミットメッセージ。本書には現在地と設計を置き、長い型一覧を追記しない。
