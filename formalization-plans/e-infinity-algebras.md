# E∞ 代数のモデル圏（レーン E2）

> **v2 の位置づけ（2026-10-19）**：E2a は foundations.md §6 の E2（E2a-3〜5 → E2b → G1′）。N は γ3c → γ4 → F2-lite（Ind・compact・冪等完備化）。

## 引き継ぎ（2026-10-19）

### N（γ1.5・γ3）
- **現在地**：γ1.5 完了。γ3b は任意の小圏で元の非反転 q_x の同値性・全導来 fiber の可縮性による両向き判定と、pinched Hom の直接 fiber 模型まで公開。
  γ3c は 𝒮 の小積・Sp の有限積（空積含む）、一脚 fibration の引き戻し、fibration の塔の ∞ 極限を公開。𝒮 の小余積・任意の span と列の ∞ 余極限も公開。
  通常の随伴と整合する単体的 Hom 同型から、任意の coherent な極限錐の極限保存を証明。豊穣右関手の coherent nerve の像との一致も公開。
  γ4 の具体例 `K × − ⊣ Map(K,−)` は通常の随伴・豊穣 Hom 同型・零単体と、両対象の anodyne Kan 置換を含む frame Hom を全単体で照合。固定した Quillen 類の保存も公開。
  一般の小図式の重み付き coend と内部 Hom の普遍性、反転係数の end との自然同型、Kan 置換後の豊穣合成を保つ Hom 比較・普遍切断点・実際の coherent 余錐を構成。
  通常の任意の小圏上の Kan 値図式では、反対錐の ∞ 極限性と元の native な余錐の ∞ 余極限性を無条件に証明。
  任意の coherent 図式の切断空間は、形状の押し出し・セル付加・骨格の塔の厳密な極限で表示。left fibration では各値は Kan、制限は Kan fibration。
  部分余極限頂点の付加・指定余錐の延長・余極限性の保存と反映、元の図式の固定頂点余錐空間の厳密な引き戻しを構成。全 Hom の制限と実際の付加比較辺の前合成の自然性も公開。
  部分余極限対象の native な Kan 値 span とその小さい Kan 押し出し候補を構成。元の三角形による指定境界経路を保つ右枝の修正・全パラメータでの厳密な貼り合わせで、元の図式の実際の余錐を構成。
  元の余錐空間と native な span の余錐空間を、それぞれ Hom の end・共通 path end と実際のホモトピー同値で比較。全 Hom 族の同値性と余極限性の必要十分条件も公開。
  比較先の native な全 Hom 族の同値性は無条件に証明済み。元の族との end 内のホモトピー入力は未構成で、指定余錐の余極限性・γ3c 全体の完了とは数えない。
  元の二単体・標準二辺・長辺・可変終点を保つ輸送三角形と全 Hom 族、底・始点・評価固定の比較円柱をデータ化。指定経路に沿う既存の左右の全 Hom 族のホモトピーと辺の類も公開。
  end の HR/HL は評価固定データから構成。任意の単射境界から同じ評価を保つ族の延長と、二つの指定円柱を二辺として保つ比較三角形を構成。
  右 HR と元の指定四面体の円柱を同じ三角形で接続。第三辺の始点の射影を既存の右 Hom 係数と同定し、終点固定円柱から native な共通脚の前合成へ接続。三辺の類の合成等式も証明。
  左は標準 prism 自身の輸送辺と実際の付加辺を保持し、native な左二単体上の実際の三角形と、終端辺・底を厳密に保つ全 Hom 族を構成。共通族との評価の一致、左 HL との二辺固定比較三角形、三辺の類の合成を証明。
  左右の元の全辺族から同じ native 根辺への比較を構成し、既存の native 比較円柱を二面に保つ三角形と、終点を全時刻固定する比較の類の一意性を証明。
  元の三角形・四面体の長辺を同じ可縮な固定延長空間へ移し、標準長辺比較の終点を元の span 輸送同型、修正辺の終点を元の境界同型へ同定。
  境界同型の実際の定義による四因子相殺で、元の左長辺から修正後の右長辺への比較の終点の類が恒等と証明。
  同じ根辺の終点評価の left fibration 性と零番ホーンの持ち上げから、同じ両端の厳密な fiber 辺へ直し、底・始点・終点の全時刻固定円柱を構成。
  元の左三角形の全 Hom 族を長辺へ制限し、底・終端係数・可変終点を保って同じ円柱全体へ延長。底は元の左根辺族と厳密に一致。
  同じ境界と底を持つ二つの全余錐族の相対比較を公開。根辺円柱の時間零の端面を、元の左長辺族へ底・終端・可変終点を全時刻固定して接続済み。時間一の端面と元の右四面体の長辺族を同じ右長辺上に置き、それぞれの底を既存の左・右根辺族へ同定。元の Hom の普遍余錐の二段制限を回収して、両族の終端係数が上の余錐空間で厳密に一致することも証明。円柱の右端面から元の右四面体族へ、上の終端係数を全時刻固定して底の全ホモトピーを持ち上げ済み。正規化した底は元の `specifiedCoconeRootFamilyComparison` の同じ raw な円柱を包含した射そのもの。根辺円柱の始点側の全族を同じ c の定値な時間辺へ制限し、底が時間に依存しないことを厳密に証明。二時刻の比較を底・可変終点の全時刻固定で構成し、元の時間零・一の端面の初期制限へ同じ raw な円柱で接続。固定終点の初期 Hom 空間へ円柱を移す一般 API と、包含・評価・底の raw な式も公開。元の左右の長辺の初期 Hom 族を三角形・四面体の既存の族へ厳密に同定し、左右と中央の三つの比較を同じ固定終点の初期 Hom 空間へ移送済み。左の逆・中央・右の比較同型を合成し、評価像は元の共通全族の恒等射、底の像は元の右比較の像と同じ Arrow であることを証明。右の底を元の初期射影比較の同じ raw な円柱へ同定。評価上で厳密に定値な代表を構成し、h Fun の忠実性で元の三因子の指定類と底の類を保持した。左右の元の Hom 円柱と native 比較同型の積が同じ Arrow であることを証明。元の HL・HR と公開済み native 円柱を四辺に保つ実際の正方形を構成。左右で同じ共通円柱を選び、二つの指定合成三角形も構成。path end の「元の逆代表を選んでから前合成」の raw な円柱と逆の類を照合し、同じ共通円柱と native 定値辺へ結ぶ左右の正方形まで構成。元の左右の全辺族の初期 Hom への制限、評価・底の厳密な式、同じ実際の脚へ射影する評価固定の枝比較円柱も構成。初期 Hom の後合成自然性から、左右の枝の初期族を共通部分へ制限したものが、元の左根辺三角形の中頂点と右四面体の同じ枝始点の全族に厳密に一致すると証明。実際の比較辺を初期 Hom 空間上で前置する写像を相対切断から構成し、評価と底の既存の Hom 前合成を厳密に保持。元の左右の枝円柱の前置像も構成し、共通評価の全時刻固定と元の枝 Hom 円柱の raw な前合成像を証明。既存の `InitialHomEdgeCylinder` を同じ全辺族・終点・底・初期包含を保持するデータへ強化し、普遍相対切断との終点・底固定比較も構成。同じ全辺族の比較を初期 Hom へ制限し、既存データの `lift` そのものを終点に保ち、評価と底の全時刻固定も証明。初期 Hom のパラメータ前合成自然性と普遍前置の始点の厳密な式を証明し、元の HL・HR の同じ lift へ評価・底固定で接続。評価固定三円柱の合成則と恒等因子の相殺により、普遍前置から作る Hom 円柱が元の制限円柱と同じ Arrow の類を与えると証明。左右の同じ共通全 Hom 族への前合成後も、元の HL・HR の類と raw な初期射影を保持する円柱まで公開。共通 end 内の全族のホモトピーは未完了。
  一般の γ4 も未完了。F2-lite 第2部は10-20に F1b へ移管（`foundations.md` §6、`infinity-core-F2.md` §3）。
- **残り**（依存順・時間は再開後の概算）：
  1. γ3c：通常の小圏上の Kan 値図式の coend 余極限から、任意の coherent な図式への接続。HTT 4.2.4.1、Kerodon 7.5.4.6、20〜50時間。
  2. γ4：具体例を一般の simplicial Quillen 随伴の cofibrant-fibrant 置換・frame へ拡張する。HTT 5.2.4.6、8〜20時間。
  3. 2 と F1b の随伴 API から導来 ∞ 随伴の単位・余単位・整合性と一般の右導来関手の極限保存を構成する。HTT 5.2.4.6、Kerodon §6.2、12〜30時間。
  4. E2a-3・4 と γ2 の豊穣化の確定後、Alg_E と忘却関手へ適用する。HTT 1.1.5.10・4.2.4.1・5.2.4.6、16〜40時間。E2a の現状は下記参照。
- **主要宣言**（名前のみ。名前空間 SerrePositivity.InfinityCategories.HomotopyLimits）：
  `strictCoherentCone_isLimit_iff_general_comparisonFiber`、`strictConePinched_generalOriginalEnd_equivalence`、
  `spaceProductCone_isLimitCone`、`spacePullbackCone_isLimitCone`、`spaceTowerCone_isLimitCone`、
  `spaceArbitraryPushoutCocone_isColimitCone`、`spaceArbitrarySequentialColimitCocone_isColimitCone`、
  `SimplicialAdjunctionHomIso`、`strictDiagram_limitCone_postcomp_isLimit_of_adjunctionHomIso`、
  `kanTensorAdjunctionHomIso`、`kanInternalHom_map_isLimit`、`kanReplacedTensorFrameAdjunction_square`、
  `reflectedWeightedColimitHomIso`、`bousfieldKanCoherentConeComparison_homotopyEquivalence`、
  `bousfieldKanCoherentCocone`、`bousfieldKanCoherentCocone_vertex`、
  `coherentCone_isLimit_iff_reflectedNativeComparison`、`coherentConeFamily_homotopy_over_apex`、
  `coherentCone_isLimit_of_family_lifts`、`bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts`、
  `kanReflectedBousfieldKanColimitHomComparison_of_point`、`bousfieldKanCoherentConePoint_of_end_point`、
  `coherentCosliceSourcePrecomposition_weighted`、`coneIdentityCosliceSection`、
  `bousfieldKanCoherentConeSourceFamily_restrict`、`bousfieldKanCoherentOppositeCone_isLimit`、
  `bousfieldKanCoherentCocone_isColimit`、`kanDiagramCoherentNerve_hasColimit`、
  `skeletalSectionCone_isLimit`、`skeletalSectionDiagram_map_fibration`、`skeletalCellSectionCone_isLimit`、
  `colimitAttachedCocone`、`colimitAttachmentComparison_restrict`、`colimitAttachmentApexHom`、
  `cosliceShapePushoutIso`、`coconeMappingShapePushoutIso`、`coconeMappingShapeCone_isLimit`、
  `initialRestrictionHomComparison_square`、`colimitAttachmentHomPrecomposition`、
  `coconeMappingSpaceHomComparison_restrict_square`、
  `partialColimitCoconeToHomEnd`、`partialColimitCoconeToHomEnd_homotopyEquivalence`、
  `spanNerveHornIso`、`partialColimitSpanHomEndIso`、
  `partialColimitOriginalToNativeSpanCocones_homotopyEquivalence`、
  `coconePointHomFamily_restriction_homotopy`、`coconePointHomFamily_comparison_homotopy`、
  `exists_partialColimitPushout_cocone_with_branch_homotopies`、`coconeBoundaryPathRectifiedFamily`、
  `coconeBoundaryPathCorrection_unique_homotopy`、`partialColimitSpanBoundaryPath`、
  `partialColimitSpecifiedPathCocone`、`isColimitCone_iff_partialColimitHomFamilyToPathEnd`、
  `nativeSpanUniversalFamilyToPathEnd_homotopyEquivalence`、`specifiedPathCocone_isColimit_of_pathFamily_homotopy`、
  `partialColimitSpanLeftTransportHomComparison`、`partialColimitSpanRightTransportHomComparison`、
  `specifiedCoconeCommonHomFamily_rootPrecomposition_homotopy`、
  `partialColimitSpanTransportHomPathComparison`、`specifiedCoconeRightNativeIso`、`specifiedCoconeLeftRootedHomFamily_base`、`specifiedCoconeLeftRestrictionTriangle_homMk_comp`、`specifiedCoconeLeftNativeIso`、`specifiedCoconeRootFamilyTriangle_homMk_comp`、`fixedExtensionEndpointHomotopy_hom`、`colimitAttachmentTransportHomotopy_hom`、`specifiedCoconeRootedRightTetrahedron_standardEdge`、`coconeBoundaryTransportHomotopy_hom`、`fixedExtensionRestriction_endpoint`、`specifiedCoconeLeftTriangleComparisonExtensionEdge_long_homMk`、`prismTransportIso_parameter_hom_arrow`、`prismTransportIso_standard`、`specifiedCoconeLeftTerminalTransport_square`、`functorIsoComponent_point_hom_arrow`、`specifiedCoconeLeftTerminalTransport_actual_hom_arrow`、`specifiedCoconeLeftTerminalTransport_standard_hom_arrow`、`specifiedCoconeLeftFirstEndpointHomotopy_hom`、`specifiedCoconeLeftMiddleComparison_hom_arrow`、`specifiedCoconeLeftTerminalComparison_hom_arrow`、`specifiedCoconeRightPrefixTerminalComparison_hom_arrow`、`specifiedCoconeRightCorrectionFace_second`、`specifiedCoconeRightCorrectionFace_projection`、`specifiedCoconeRightCorrectionExtensionEdge_uncurry`、`specifiedCoconeRightCorrectionExtensionEdge_boundary_edge`、`specifiedCoconeRightCorrectionExtensionEdge_canonical_hom_arrow`、`fixedExtensionBaseIso_uncurry`、`specifiedCoconeLeftCommonRootRestriction_uncurry`、`specifiedCoconeRightPrefixCommonRootRestriction_actual`、`specifiedCoconeLeftCommonRootComparisonIso_boundary_hom_arrow`、`specifiedCoconeRightPrefixCommonRootComparisonIso_boundary_hom_arrow`、`coherentTransportPointComparisonExtensionEdge_uncurry`、`coherentTransportPointCanonicalComparison_endpoint_hom_arrow`、`specifiedCoconeStandardRootComparisonIso_endpoint_hom_arrow`、`specifiedCoconeCorrectionCanonical_boundary_hom_arrow`、`partialColimitSpanBoundaryIso_factors`、`contractibleVertexIso_endpoint_cancel`、`specifiedCoconeRootClosingComparisonIso_endpoint_hom_arrow`、`specifiedCoconeRootClosingExtensionEdge_uncurry`、`specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow`、`relativeFunctorPairRestriction_leftFibration`、`fixedExtensionEdgeTarget_leftFibration`、`specifiedCoconeRightRootEndpoint_leftFibration`、`leftFibration_correct_edge_of_identity_arrow`、`specifiedCoconeRootVerticalHomotopy_raw`、`specifiedCoconeRootVerticalHomotopy_terminal`、`relativeRetractCosliceFamily`、`fixedTerminalHomotopyFamily`、`specifiedCoconeLeftRootTotalFamily_base`、`specifiedCoconeRootVerticalFamily_terminal`、`specifiedCoconeRootVerticalFamily_base`、`specifiedCoconeRootVerticalFamily_projection`、`exists_relativeCosliceFamilyHomotopy`、`fixedTerminalHomotopyStartComparison`、`specifiedCoconeRootVerticalStartComparison_base`、`specifiedCoconeRootVerticalStartComparison_terminal`、`specifiedCoconeRootVerticalEndFamily_base`、`specifiedCoconeRightRootTotalFamily_base`、`pointRestrictionEdgeFamily_uncurry`、`specifiedCoconeRootTotalFamilies_tip_uncurry`、`specifiedCoconeRootVerticalEndFamily_right_terminal`、`exists_specifiedHomotopyLift`、`exists_relativeCosliceSpecifiedHomotopy`、`specifiedCoconeRootBaseFamilyComparison_terminal`、`specifiedCoconeRightRootBaseComparison_raw`、`specifiedCoconeRootVerticalEndComparison_terminal`、`specifiedCoconeRootVerticalEndComparison_native_base`、`cosliceRetractionFamily_base`、`cosliceRetractionSectionComparison_base`、`specifiedCoconeRootVerticalInitialFamily_base`、`specifiedCoconeRootVerticalInitialFaceComparison_raw`、`specifiedCoconeRootVerticalInitialFaceComparison_base`、`initialDiagramHomFamilyHomotopy_ι`、`initialDiagramHomFamilyHomotopy_base`、`initialDiagramHomFamily_restrict`、`specifiedCoconeLeftRootTotalFamily_initial`、`specifiedCoconeRightRootTotalFamily_initial`、`specifiedCoconeRootStartInitialHomotopy_base`、`specifiedCoconeRootEndInitialHomotopy_base`、`specifiedCoconeRootMiddleInitialHomotopy_evaluation`、`specifiedCoconeRootInitialComparisonIso`、`specifiedCoconeRootInitialComparisonIso_evaluation_hom_arrow`、`specifiedCoconeRootInitialComparisonIso_base_hom_arrow`、`specifiedCoconeRootEndInitialHomotopy_native_projection`、`trivialKanFibration_postcomp_iso_hom_injective`、`specifiedCoconeRootEvaluationHomotopy_evaluation`、`specifiedCoconeRootEvaluationHomotopy_hom`、`specifiedCoconeRootEvaluationHomotopy_native_hom_arrow`、`evaluationFixedHomotopyTriangle_homMk_comp`、`specifiedCoconeRootHomCylinder_native_comp`、`specifiedCoconeNativeHom_comp_hom_arrow`、`nonempty_functorHomSquare_of_homEq`、`specifiedCoconeLeftEndHomotopy_raw`、`specifiedCoconeRightEndHomotopy_raw`、`specifiedCoconeNativeEndHomSquare`、`specifiedCoconeCommonNativeHomotopy_hom`、`specifiedCoconeLeftCommonNativeTriangle`、`specifiedCoconeRightCommonNativeTriangle`、`homotopyPrecompInverseTransport_raw`、`homotopyPrecompInverseTransport_hom`、`specifiedCoconeLeftEndInverseHomotopy_raw`、`specifiedCoconeRightEndInverseHomotopy_raw`、`specifiedCoconeLeftInverseNativeHomSquare`、`specifiedCoconeRightInverseNativeHomSquare`、`pointRestrictionInitialHomFamily_ι`、`pointRestrictionInitialHomFamily_projection`、`pointRestrictionFullHomCylinder_projection`、`specifiedCoconeLeftBranchHomotopy_projection`、`specifiedCoconeRightBranchHomotopy_projection`、`initialDiagramHomFamily_postcomp`、`specifiedCoconeLeftBranchCommonInitialFamily_triangle`、`specifiedCoconeRightBranchCommonInitialFamily_tetrahedron`、`relativeEdgeCosliceSection_base`、`initialTotalEdgePrecomposition_evaluation`、`initialTotalEdgePrecomposition_projection`、`initialRestrictionTotalPrecomposition_pinched`、`colimitAttachmentTotalPrecomposition`、`specifiedCoconeLeftBranchToInitialHomotopy_projection`、`specifiedCoconeRightBranchToInitialHomotopy_projection`、`InitialHomEdgeCylinder.fullFamily`、`InitialHomEdgeCylinder.lift_ι`、`initialHomEdgeSectionComparison_target`、`initialHomEdgeSectionComparison_base`、`initialHomEdgeSectionInitialComparison_ι`、`initialHomEdgeSectionInitialComparison_evaluation`、`initialHomEdgeSectionInitialComparison_base`、`initialDiagramHomFamily_precomp`、`initialRestrictionSection_source`、`initialRestrictionSectionComparison_base`、`initialRestrictionUniversalHomCylinder_hom_arrow`、`colimitAttachmentUniversalHomCylinder_hom_arrow`、`specifiedCoconeLeftUniversalInitialHomotopy_evaluation`、`specifiedCoconeRightUniversalInitialHomotopy_evaluation`、`specifiedCoconeLeftUniversalHomotopy_projection`、`specifiedCoconeRightUniversalHomotopy_projection`、`specifiedCoconeLeftUniversalHomotopy_hom_arrow`、`specifiedCoconeRightUniversalHomotopy_hom_arrow`。
- **依存と提供**：Core・F1（coherent Hom、切断、edgewise、通常の豊穣関手）、F1b（trivial fibration 上の相対ホモトピー）、Stable、KST/Spectra、Simplicial の小対象分解を読み取り専用で使用。
  提供先は F2 の 𝒮、L9／K-Sp の Sp、E2b。集約は InfinityCategories/HomotopyLimits.lean、監査は scripts/audit_homotopy_limits.lean。
  型は Lean、運用規約は foundations.md §8。README に実施記録は追記しない。
- **未コミット**：今回の保存単位は初期 Hom のパラメータ前合成、普遍前置の始点と元の lift の比較、同じ類の回収、実際の付加辺への適用、左右の共通 Hom 族への制限の9新規モジュール、集約・監査、本 N 節。保存後は N 所有の変更なし。F2 計画は F1b 所有のため保存対象外。共有計画は N 節だけをステージする。
  root の迷子 RelativeFreePathBoundary は正しい場所に修正版がコミット済みの N 旧稿と確認し、削除済み。
- **既知の問題**：停止時の対象ビルド・監査に失敗なし。新規 sorry・追加公理・公開名衝突なし。監査の既存の重複1件を除去済み。
  今回の公開型に ModelCategory SSet や IsRightQuillen の追加仮定なし。SSet の充填性・cofibrancy は Mathlib の固定 Quillen 類を使用。root 全体は未検証。
  完全なモデル構造の存在を与える `Inputs/Homotopy/KanQuillen.lean` は既存 sorry を含むので主経路へ import しない。
  今回はその存在命題を使わず固定類の保存と Hom 比較を証明しており、一般のモデル圏からの導出を済ませたとは数えない。
  γ4 用の Hom 同型は y に全単体で自然、x の高次豊穣自然性は未要求。従って通常の Quillen 条件だけからの ∞ 随伴の完成とは数えない。
  Sp では指定した Hom の局所 Kan 性・Ω 条件・cofibrancy を保持。一般の図式と右導来関手の cf 置換・高次整合性は後続課題。
  `(edgeTransport_composition_iso p σ).some` は同じ三辺の異なる σ でも同じ値となることを Lean の rfl で確認。選択した同型だけでは元の二単体の高次情報が残らない。
  `partialColimitSpanTransportIso` は実際の三角形 prism・相対円柱から作る同型へ差し替え済み。end 比較の HR/HL は評価固定の中間円柱データから構成する形へ差し替え済み。右 HR と元の四面体の比較円柱は、二辺を固定した実際の三角形で接続し、その辺の類の合成を証明済み。既存の右 Hom 係数から native な共通脚への接続も構成。左 HL と実際の左二単体の全 Hom 族も二辺固定三角形で接続済み。左側も同じ native な共通脚への接続を構成済み。指定経路の高次照合は未完了。`SpecifiedCoconeBranchData` は標準 prism 自身の左右辺との一単体の一致も保持する構成へ強化済み。右修正三角形は同じ標準辺と元の修正辺を指定して充填する。
  大きい native 頂点・脚の型照合では `SpecifiedCoconeLeftTerminalComposition` と同様に、選択した span の候補・脚を局所的に irreducible とし、内部構成の反復展開を避ける。
  依存が壊れたら回避せず停止する。他レーンの作業中変更はコミットしない。
- **次の一手**：`specifiedPathCocone_isColimit_of_pathFamily_homotopy` の全終点の族のホモトピー入力を構成する。
  元の族は `partialColimitHomFamilyToPathEnd`、同じ頂点で表示した比較先は `specifiedCoconeNativeFamilyToPathEnd`。
  後者の同値性は無条件に証明済み。前者とのホモトピーを仮定した定理は、余極限性の完成とは数えない。
  元の指定経路の左右の全 Hom 族と native 根辺への比較円柱は構成済み。三角形・四面体の同じ実際の辺を保ち、終点の輸送同型の四因子相殺から得た `specifiedCoconeRootVerticalHomotopy` は底・始点・終点を全時刻固定する。
  `specifiedCoconeRootVerticalStartComparison` は時間零の端面を元の左長辺族へ結び、底・終端・可変終点を全時刻固定する。
  時間一の `specifiedCoconeRootVerticalEndFamily` と元の `specifiedCoconeRightRootTotalFamily` は同じ右長辺上にあり、底はそれぞれ元の左・右根辺族。`specifiedCoconeRootVerticalEndFamily_right_terminal` で、上の終端係数の厳密な一致まで証明済み。
  右端面の照合は `specifiedCoconeRootVerticalEndComparison` まで構成済み。上の終端係数と可変終点を全時刻固定し、底は元の左右の全比較円柱を厳密な図式の等式で表示変更したもの。`_native_base` で元の `specifiedCoconeRootFamilyComparison` の同じ raw な円柱の包含と一致する。
  始点側の照合は `specifiedCoconeRootVerticalInitialFaceComparison` まで構成済み。元の初期時間辺の底が定値であることを全族で証明し、二時刻の比較を同じ円柱の時間零・一の端面の初期制限へ移した。底と可変終点は全時刻固定。元の根辺円柱そのものを全 Hom の円柱へ変換したと取り違えず、同じ全余錐族の二切断の相対比較であることを保持する。
  三比較の同じ初期 Hom 空間への移送と合成は `specifiedCoconeRootInitialComparisonIso` まで構成済み。元の左三角形・右四面体の初期 Hom 族との一致は `specifiedCoconeLeftRootTotalFamily_initial`・右版で厳密に証明。左右と中央の元の raw な円柱の制限は各 `_ι` で保持する。
  合成同型の評価像と底の像の計算に、`specifiedCoconeRootEndInitialHomotopy_native_projection` の raw な一致を合成し、元の初期射影比較の同じ類へ同定済み。
  `specifiedCoconeRootEvaluationHomotopy` は同じ左右の族を結ぶ厳密な評価固定代表。`_hom` で三因子の合成の同じ類、`_native_hom_arrow` で底の指定類を保持する。自明 Kan 評価の後合成が h Fun で忠実であることを使う。
  同じ評価固定の三円柱の合成則から `specifiedCoconeRootHomCylinder_homMk_comp`、元の根辺三角形との合成から `_native_comp` を証明。左右の制限三角形をつなぎ、`specifiedCoconeNativeHom_comp_hom_arrow` で元の HL・HR（全 Hom の制限を前合成）と公開済み native 比較同型との積を同じ Arrow へ同定済み。端点の輸送は `kanFunctorIsoTransport_hom_arrow`、元の円柱の保持は各 `_ProjectedCylinder_raw` を用いる。
  指定四辺の実現は `specifiedCoconeNativeEndHomSquare` まで構成済み。`specifiedCoconeLeftEndHomotopy`・右版は同じ共通始点を持ち、各 `_raw` で元の HL・HR の全 Hom 制限を厳密に保つ。Stable の `exists_stableSquare_of_homMk_comm` を関手単体集合へ適用する。
  `specifiedCoconeCommonNativeHomotopy` は左 HL と元の左 native 同型の積の代表。左右の `specifiedCoconeLeftCommonNativeTriangle`・右版は同じ共通代表と公開した同じ native 円柱を三辺に保つ。
  path end の逆代表は `specifiedCoconeLeftEndInverseHomotopy`・右版へ移送済み。各 `_raw` は元の HL・HR の逆同型の代表を先に選び、後から全 Hom の制限を前合成した射そのもの。`_hom` は順方向円柱の逆の類と同定する。`specifiedCoconeLeftInverseNativeHomSquare`・右版はその同じ逆円柱を下辺、共通代表を右辺、native 比較を左辺、native 定値円柱を上辺に保つ実際の正方形。
  枝の元の全辺族から `specifiedCoconeLeftBranchHomCylinderData`・右版を構成済み。`pointRestrictionInitialHomFamily` は同じ全辺族の初期制限で、`_ι`・`_evaluation`・`_projection` は元の族・枝への制限・実際の脚の前合成を厳密に保持する。枝比較の各 `_projection` は同じ評価固定中間円柱の raw な射影。
  枝の初期族の共通制限は `specifiedCoconeLeftBranchCommonInitialFamily_triangle`・右の `_tetrahedron` で、元の根辺三角形の中頂点と四面体の同じ枝始点の初期族へ厳密に同定済み。元の終端辺・終端面の族を uncurry で回収し、`initialDiagramHomFamily_postcomp` を適用する。これらの枝始点は共通部分の始対象 c ではない。
  前置は `initialTotalEdgePrecomposition` と `initialRestrictionTotalPrecomposition` まで構成済み。相対 coslice の終点切断を直接使い、初期 Hom 空間全体を一度に入力する。始点・終点の始対象性は不要。`colimitAttachmentTotalPrecomposition_pinched` は底を既存の実際の付加辺の前合成へ厳密に同定する。左右の `specifiedCoconeLeftBranchToInitialHomotopy`・右版は元の枝の同じ円柱を共通始対象 c の初期 Hom 空間へ写す。各 `_evaluation` は同じ共通族を全時刻固定し、`_projection` は元の枝 Hom 円柱に既存の付加辺の前合成を続けた同じ raw な射。
  `InitialHomEdgeCylinder` は元の相対持ち上げの全辺族と `full_target`・`full_base`・`lift_ι` を保持する形へ強化済み。`initialHomEdgeSectionComparison` は、底の族が同じ `cosliceEdgeSection` の像の場合に、普遍相対切断の像とその同じ全辺族を終点・底固定で結ぶ。選択した切断の前合成自然性は仮定しない。
  `initialHomEdgeSectionInitialComparison` は保持した同じ全辺族の比較を初期 Hom 空間へ制限した円柱。終点は元のデータの `lift` そのもので、`_ι` は同じ raw な制限、`_evaluation`・`_base` は評価と底を全時刻固定する。
  始点側は `initialDiagramHomFamily_precomp`・`initialRestrictionSection_source` と `initialRestrictionSectionComparison` で厳密に接続済み。比較の終点は元の同じデータの `lift`、評価と底は全時刻固定。`initialRestrictionUniversalHomCylinder_hom_arrow` は評価固定三円柱の合成を底へ写して恒等因子を消し、元の HL・HR の同じ類を回収する。実際の付加辺への適用は `colimitAttachmentUniversalCylinderData`・`colimitAttachmentUniversalHomCylinder`。左右の `specifiedCoconeLeftUniversalInitialHomotopy`・右版は同じ共通評価から `(U ≫ section_B) ≫ Φ` へ至る。各 `_evaluation` は全時刻固定、`specifiedCoconeLeftUniversalHomotopy_projection`・右版は同じ raw な射影、各 `_hom_arrow` は元の `specifiedCoconeLeftEndHomotopy`・右版の同じ類を回収する。
  次は終点側：元の根辺三角形・四面体の付加辺面を使い、前置後の枝終点族と元の根辺初期族を底の native 二単体を保って比較する。一般には実際の辺族 L と、その終点制限を `relativeEdgeCosliceSection` で戻した族 K を比較する。底では `cosliceEdgeFamilyComparison` を使って K の底から L の底へ同じ終端を固定して結び、`exists_relativeCosliceSpecifiedHomotopy` で同じ両端・終端を保って持ち上げ、`initialDiagramHomFamilyHomotopy` で始点へ制限する。K の底が同じ canonical section の像であることと終端の厳密な一致を先に示す。底の比較の類は `cosliceEdgeFamilyTriangle_homMk_comp`・終端固定の一意性を使い、元の L の切断比較の逆の同じ類へ同定する。左右の実際の付加辺面へ代入し、枝の初期族の共通制限は既存の `_triangle`・`_tetrahedron` で照合する。始点比較・枝円柱の像・終点比較を同じ初期 Hom 空間で合成し、公開した native 比較と枝 Hom の前合成像の類を照合してから共通 end 内で貼る。
  可変終点固定の比較の一意性は、全時刻の固定または同じ射の像の等式を実証してから適用する。型や両端の一致だけから同じ全族・同じ類とは推論しない。任意の代表を底で正しいものと扱わない。
  同じ経路の持ち上げの相対ホモトピーを共通 end に移して入力を閉じる。その後、骨格の無限段階とセルの添字の小ささを処理。
  任意の coherent 図式の余極限性を閉じてから γ4・Sp/E2b への提供へ進む。F2-lite 第 2 部は F1b の所有範囲として重複実装しない。

### E2a（既存の引き継ぎ）

- **現在地**：E2a-0（Ch(A) の射影モデル構造）、E2a-1（オペラッド・自由代数随伴）、
  E2a-2（Barratt–Eccles オペラッド・augmentation）まで完了。
  E2a-3 は承認済みの Hopf オペラッド＋区間＋path object 経路で、工程 (1) が完了。
  一般の小さい単体集合の正規化 AW 対角の鎖写像・自然性・余結合性・左右余単位と、
  一般 shuffle 鎖写像の AW 余代数射性を検証し、整数模型へ移送済み。
  `partialComposition_diagonal_tensorμ` が既存 BE 部分合成の余積適合性を与える。
  arity ごとのテンソルオペラッド `Operad.hadamard` を、両単位則・内外等変性・
  入れ子と独立な代入の結合則を含めて構成。頂点の群状元公式から単位保存を証明し、
  `hopfDiagonal` を実際の E → E ⊗ E のオペラッド射に束ねた。
  `BarrattEccles.hopf` はこの対角、既存の E → Com、余結合性・左右余単位則を持つ。
  Σ_n 同変性は対称列の自然性に含まれ、余可換性は要求しない。
  工程 (2) は P-coalgebra・射の圏・忘却関手・オペラッド射に沿う制限を構成済み。
  `CoalgebraInterval` は実際の余代数・二端点・収縮・余演算の保存図式と、
  底の境界 cofibration・収縮の擬同型からなる。区間の制限も構成済み。
  convolution の反復評価とその両変数自然性、各 arity の演算 chain map は構成済み。
  底の Hom(H,B) の `prepathComplex`、定数射と両端点評価の自然性も検証済み。
  単位則・全置換の等変性・代数射の後合成による全演算の保存を検証済み。
  `convolutionAction_comp` で全位置の部分合成則を閉じ、`convolutionAlgebra` を構成。
  前合成・後合成を代数射と `convolutionFunctor`・`convolutionPreNat` へ束ねた。
  `unitCoalgebra ε` は任意の augmentation の単位余代数。`convolutionUnitNatIso` は
  Hom(単位,B) ≅ B を自然な P 代数同型にする。区間の端点・収縮も余代数射に束ねた。
  `prepathAlgebra` は全代数の自己関手と自然な定数・両端点評価を持ち、底の既存の射と厳密に一致。
  `evaluationPair_projectiveFibration` は底の二端点評価の対が射影 fibration であることを示す。
  `constant_quasiIso` と `evaluation_quasiIso` は任意の値域で定数射・両評価の底の擬同型性を示す。
  単位の cofibrancy、端点の鎖ホモトピー逆、符号付き Hom 前合成の移送から導出済み。
  `Algebra.binaryProductIsLimit`・`terminalAlgebraIsTerminal` で積・終対象を底の複体に構成。
  `pathAlgebra` は全代数の good path object。忘却の逆像の弱同値・fibration は局所選択。
  `fibrations_llp_quasiIso` は retraction と逆合成の path から底の擬同型性を示す。
  自由像の `freeGeneratingTrivialCofibrations_cell_acyclicity` は任意の始域で成立。
  一般の極限余極限・自由像の小対象性・転送定理の適用は未完成。
  E2a-3 の工程 (2) の転送と工程 (3)・(4)、E2a-4・5、E2b・G1′ は未完成。
  現在地のコードと検証は本節と同じコミットに保存。E2a-2 完了は `60541ccb`。
- **残り**（依存順。時間は再開後の粗い実装見積もり）：
  1. 代数の積と終対象を底で構成し、忘却関手との比較から good functorial path object を完成。
     続いてこの path object から底のホモトピー同値性を示し、
     小対象性・一般の極限余極限と転送の適用を閉じる。J-cell acyclicity は構成済み。
     Berger–Moerdijk（BM）2003 命題 4.1・§4.6.3、BF §3.1、24〜60 時間。
  2. TR : E → χ のオペラッド射性を一般に証明し、χ の区間切断作用を Δ¹ に適用する。
     BF §1.3・§3.1 と McClure–Smith の区間切断作用、80〜200 時間。
     着手前にファイル数・主要補題の見積もりを計画に一段落で記す指示が未実施。
     Δ¹ の作用は必要次数 r ≤ n に特殊化してよい。TR 自体は一般に証明する。
  3. 具体区間を抽象界面へ代入して E2a-3 を完成。BM 命題 4.1、BF §3.1、8〜24 時間。
  4. E2a-4：右 Quillen、全対象 fibrant、底での homotopy 引き戻し、H⁰ の可換環構造、
     離散可換代数の E 代数化。BM 命題 4.1、BF §3.1、16〜40 時間。
  5. E2a-5：homotopy function complex と π₀ の Hom 比較。
     Hovey §5・Dwyer–Kan、既存 HomotopyFunctionComplex の具体的適用、12〜24 時間。
  6. E2b：CAlg_R := N^hc と U : CAlg_R → D(R)、離散対象と極限。
     HTT §1.1.5・§5.2.4、γ2・γ4 の適用、16〜40 時間。その後 G1′（界面の述べ直し）。
- **主要宣言**（名前のみ）：
  `SerrePositivity.EInfinity.projectiveModelCategory`、
  `SerrePositivity.EInfinity.Operad.freeAlgebraAdjunction`、
  `SerrePositivity.EInfinity.Operad.Hopf`、
  `SerrePositivity.EInfinity.BarrattEccles.operad`、
  `SerrePositivity.EInfinity.BarrattEccles.augmentation`、
  `SerrePositivity.EInfinity.BarrattEccles.hopf`、
  `SerrePositivity.EInfinity.Operad.Coalgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraHom`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict`、
  `SerrePositivity.EInfinity.Operad.convolutionAlgebra`、
  `SerrePositivity.EInfinity.Operad.convolutionFunctor`、
  `SerrePositivity.EInfinity.Operad.convolutionPreNat`、
  `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat`、
  `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso`、
  `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono`、
  `SerrePositivity.EInfinity.homPrecompose_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration`、
  `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso`、
  `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_cell_acyclicity`。
- **依存と提供**：HomotopicalAlgebra の Transfer/Recognition・Transfer/Right・
  HomotopyFunctionComplex、Spectra/SymmetricSequence、DifferentialGraded の
  Cells・複体のテンソル・HomComplex を読み取り専用で使う。
  提供済みは局所選択する Ch(A) のモデル構造、自由代数随伴、実際の E と E → Com、
  E の Hopf 構造、余代数区間の界面、全代数の good path object と J-cell acyclicity。
  Alg_E のモデル構造・右 Quillen U・CAlg は未提供。
- **未コミット**：本レーンのコード・監査・README・この節は全て同じコミットに保存。
  他レーンの root・DG・HA・InfinityCategories 等の変更は温存し、コミットしない。
- **既知の問題**：対象ビルド成功（2778 jobs）、公理監査成功（5600 宣言、標準 3 公理のみ）。
  新規 sorry・追加公理・名前衝突はなく、572 モジュールの import 閉包に他レーンの未コミット依存はない。
  今回の宣言に `ModelCategory`・`IsRightQuillen` 仮定はない。
  Ch(A) のモデル構造は局所的に選び、global instance を追加しない。
  一般の正規化 AW API は SSet.{0} と ModuleCat.{u} A を使う。
  正規化モデルは商表示ではなく Moore 部分複体であり、降下補題を使う。
  始域の cofibrancy は追加せず、完全なモデル構造を維持する。
  Hinich 4.1.1 は使わない（正標数で E は Σ-split でない）。
  全体 root ビルドは今回の検証範囲外。他レーンの import 閉包が壊れたら回避せず停止する。
- **次の一手**：工程 (2) の一般の極限余極限と自由像の小対象性を構成する。
  極限は `Algebra.ofJointlyMonicActions` と底の極限錐を使い、忘却が極限を作ることを示す。
  余極限は自由・忘却随伴の代数的表示、filtered 余極限とテンソル冪・coinvariant の保存を使う。
  自由像の I・J の小対象性を得て、`Transfer.Right.rightTransfer` へ
  `freeGeneratingTrivialCofibrations_cell_acyclicity` を渡す。TR・具体区間には未着手。

作成日：2026-10-18。状態：計画。ε の経路として E2（モデル圏）を採用（2026-10-18 決定）。
全体の正本は [infinity-categories.md](infinity-categories.md) §0・§5。

## 0. 位置づけ

G1 の界面（perfectoid 化とその性質の束）を述べる場である CAlg_R を、
Ch(R) 上の E∞ オペラッド（Barratt–Eccles）の代数のモデル圏で実現する。
三段で進める。

| 段 | 内容 | 使い先 |
| --- | --- | --- |
| E2a（モデル圏まで） | オペラッド・Barratt–Eccles・E∞-dg 代数・転送モデル構造・右 Quillen な忘却関手・homotopy function complex | 界面の欄を「Alg_E の homotopy 引き戻し」「homotopy 写像空間」で述べる。γ を待たずに G1 の CAlg 版へ昇格できる |
| E2b（∞ 圏化、γ） | Alg_E の cofibrant 対象の単体的豊穣化と coherent nerve、homotopy 極限 = ∞ 極限、Quillen 随伴 = ∞ 随伴 | 界面を Lurie の言葉（quasicategory の引き戻し）で述べる。K 理論の Sp と共有 |
| E2c（BS の続き用） | 余単体的 E∞-dg 代数の Tot と余単体的可換環への E∞ 作用（Berger–Fresse）、単体的可換環のモデル圏と多項式解像度 | BS §4・§7・§8 の構成 |

E1（∞ オペラッド）は採らない。後で HA の定理を文字どおり引用したくなった場合に、
E2b ≃ E1 の比較（HA 4.5.4.7 型の rectification）を任意項目として検討する。

## 1. 既存資産

- `HomotopicalAlgebra/`：Mathlib `ModelCategory` 上の Quillen 随伴（H1）、Under（H2）、
  転送（`Transfer/Recognition.lean`：生成類から Mathlib の `ModelCategory` を構成、acyclicity は明示仮定；
  `Transfer/Right.lean`：右随伴が fibration と弱同値を作る転送）、Smith の定理、
  Bousfield 局所化、Reedy、`HomotopyFunctionComplex/`（frame による導来写像空間）、
  `Monoidal/`（モノイダルモデル圏、monoid axiom）。
- `Spectra/SymmetricSequence/`：対称列と Day 畳み込み（オペラッドの合成積の素材）。
- `DifferentialGraded/Complexes/Cells.lean`：`complexSphere`・`complexDisk`（射影モデル構造の生成 cofibration）。
- `InfinityCategories/Derived/`：semifree の閉性（cone・fiber・直和・テンソル・底変更）。
- Mathlib：`SmallObject`、`CategoryWithCofibrations/Fibrations/WeakEquivalences`、`ModelCategory`。
- 未整備：Ch(A) の非有界射影モデル構造（Mathlib は `CochainComplex.Plus` の injective のみ）、
  オペラッド、対称群作用つき複体。

## 2. E2a の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| E2a-0 | Ch(A) の非有界射影モデル構造：弱同値 = 擬同型、fibration = 各次数全射、生成 cofibration `complexSphere (n+1) → complexDisk n`、生成 trivial cofibration `0 → complexDisk n`。`Transfer/Recognition.lean` で構成 | Hovey, Model Categories 2.3.11 |
| E2a-1 | Ch(A) 上の対称オペラッド：各 arity n の複体 P(n) と Σ_n 右作用、合成、単位。代数、代数の射、自由代数 Sym_P（⊕ (P(n) ⊗ A^{⊗n})_{Σ_n}）、自由 ⊣ 忘却 | Loday–Vallette、Berger–Moerdijk 2003 §1 |
| E2a-2 | Barratt–Eccles オペラッド E：EΣ_n（Σ_n の translation 亜群の nerve）の正規化鎖。各 arity が可縮、Σ-cofibrant（各 E(n) が Σ_n 上自由な次数ごとの基底を持つ）、E → Com | Barratt–Eccles 1974、Berger–Fresse 2004 §1 |
| E2a-3 | Alg_E の完全な転送モデル構造：弱同値・fibration は忘却で作る。AW 対角による E の Hopf 構造と E-coalgebra 区間の抽象界面から全代数の functorial path object を構成し、fibrations.llp ⊆ 弱同値、J-cell acyclicity、`Transfer.Right.rightTransfer` の適用を先に証明。TR : E → χ と区間切断作用で N_*(Δ¹) を界面に代入する。始域の cofibrancy は追加しない | Berger–Moerdijk 2003 命題 4.1・§4.6.3、Berger–Fresse 2004 §3.1（TR は §1.3）。Hinich 4.1.1 は使用しない（正標数で E は Σ-split でない） |
| E2a-4 | U : Alg_E → Ch(A) は右 Quillen、全対象 fibrant、homotopy 引き戻し・homotopy 極限は底で計算。E 代数の H⁰ が可換環であること、離散可換代数は E 代数（E → Com 経由） | 同上 |
| E2a-5 | homotopy function complex Map^h(A, B)（`HomotopyFunctionComplex/` の frame を Alg_E に適用）、π₀ Map^h = Ho(Alg_E) の Hom | Hovey §5、Dwyer–Kan |

## 3. E2b（γ）の工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| γ1 | 局所 Kan な単体的圏の coherent nerve は quasicategory（Mathlib `SimplicialNerve` に対して） | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| γ2 | Alg_E の cofibrant 対象の単体的豊穣化（Hopf オペラッド E による B ⊗ N^*(Δ^•) 型、または Dwyer–Kan 単体的局所化）と CAlg_R := N^hc | Berger–Moerdijk 2006、Hinich、Dwyer–Kan |
| γ3 | homotopy 極限 = ∞ 極限、右 Quillen ⇒ ∞ 極限保存、Quillen 随伴 ⇒ ∞ 随伴 | HTT 4.2.4.1、5.2.4.6 |

γ2 の単体的豊穣化が E2b の最大のリスクである。E2a の完了時点で方式を決める。

## 4. 受入基準と記録

dg-nerve.md §4 と同じ（ビルド、標準 3 公理、docstring、計画への記録）。
配置は `SerrePositivity/EInfinity/`（E2a）、namespace `SerrePositivity.EInfinity`。
集約ファイルをルートに 1 行で追加する。既存の `HomotopicalAlgebra/`・`Spectra/` は編集せず、
必要な一般補題は新規ファイルに置く。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/e-infinity-algebras-log.md](archive/e-infinity-algebras-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
