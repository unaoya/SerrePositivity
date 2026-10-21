# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-21）

### 現在地

- S1〜S7（D7）完了。実境界から Q・A と二微分式を構成し、coslice の直接充填で cofiber の普遍性、任意四角形の双カルテジアン判定、全 fiber/cofiber と有限極限余極限、D(S) の実安定性を証明した。
- 実 suspension・複体シフト・接続射の符号を照合。D3 の標準 cone 三角形との比較、全 distinguished triangle の保存・反映、逆関手・単位・余単位の全整数シフト整合性を持つ三角同値を公開済み。
- β3 完了。実 Verdier over の反転の filtered 性、有限対の全境界・全時刻を保つ実 roof 比較の cofinality と弱ホモトピー同値、任意反転標的への coherent な降下を証明した。
- `dgQuotientNerveProjection_isLocalization` は任意 quasicategory 標的に対する全前合成の充満忠実性・本質的全射性を与える。局所 K-flat 性を元の Hom に仮定しない平坦分解後の商についても `resolvedDGQuotientFunctor_isLocalization` を証明した。
- 全零化完全関手 ∞ 圏との同値、実安定閉包の完全充満包含、商の零化・完全性・実安定性、局所 K-flat 商と平坦分解後の商の実 Verdier 列まで統合・公理監査済み。H⁰ の Verdier 商の同値で代用していない。
- β5：非可換 `Mon (Complex R)` の `D(A)=N_dg(Semifree(A))`、一般小 dg 圏の半自由／射影的模型の実同値と安定性、Perf の実安定性と Perf→D の完全充満包含を公開済み。
- D・Perf の実 graph tensor、射影的対象を保つ一般 dg 関手の単位・合成の全関手比較、包含との比較四角形、graph Morita 不変性、dg 代数の quasi-isomorphism 不変性まで統合・監査済み。H⁰ の同値に加え、全 source shift から全 Hom の準同型性を検証した。
- 二変数の実空間値 Hom と同じ全 Hom 複体の pinched 模型の比較、固定入力ごとの複体値 Hom を構成。`dgNerveOppositeIso` は全 HA 方程式・任意の単体作用を保持する厳密な反対圏比較であり、dg 関手に厳密自然。実反対 ∞ 圏からの反変 Hom も統合・監査済み。
- Morita tensor の同じ逆関手を h Fun 内の三角式付き ∞ 右随伴に昇格。Perf→D の包含との逆関手比較も公開済み。一般 RHom の構成・同定とは区別する。
- 出力の射影性を仮定しない分解の実対象、実比較差、全 Hom の mapping cocone、全パラメータからの二射と比較 cochain の実持ち上げ・一意性、入力 Hom 射影の全準同型性を監査済み。実合成・実単位に加え、全 cochain 上の左右単位律・三重合成の結合律を証明し、実分解 dg 圏と実入力・半自由出力への dg 射影を構成した。
- 実入力射影は対象上全射、全 Hom の各次数で全射な準同型。対象だけを共通宇宙へ上げた実 nerve は自明 Kan fibration、したがって実 ∞ 圏同値。逆と実半自由出力射影から、任意の dg 加群値関手の実出力を半自由模型の全 ∞ 関手へ移し、実分解圏上の全関手比較同型も証明した。今回までの実分解 dg 圏と二射影は統合・監査済み。逆を実自明 Kan fibration の厳密切断へ統一し、各値から元の同じ入力像への次数別全射な準同型を回収した。
- 固定始域・固定終域の実 D(R) 値共変・反変 Hom を構成し、各頂点値が同じ厳密切断の半自由分解であることを証明した。実 augmentation は元の全 Hom end 複体への全射準同型。両分解複体の pinched 模型から元の実導来 ∞ 圏の写像空間への全空間同値も証明し、統合・公理監査済み。固定入力の両側の F1 Hom∞ との全関手比較は次項で完成。二変数の D(R) 値統合は未証明。
- augmentation の実比較 cochain の全微分式・単位零・符号付き合成則から、同じ切断補正和の全候補の HA 方程式を証明し、実単体へ昇格した。任意の単調添字変更について、単射部分の切断点・左右次数・符号と係数を照合し、非単射部分では潰れる辺の単位と高次退化の零を証明した。全ての面・退化に自然な実 `dgModuleAugmentationNervePrism`、同じ実両端、`dgModuleAugmentationNerveHomotopy` を構成し、集約ビルド・両公理監査済み。対象だけの `DGUniverseLift` を使い、入力対象の Small 性や元の出力の射影性を仮定しない。単位辺で同じ augmentation を回収する式と、厳密切断を通じた全実出力関手から元の関手へのホモトピーを追加した。固定始域・固定終域の D(R) 値 Hom の包含から元の全 Hom の R 加群値関手への全単体上のホモトピーを構成し、反変側は実反対 ∞ 圏へも接続した。追加3モジュールも集約ビルド・両公理監査済み。
- R の代表加群から全加群の生の nerve への写像空間関手を構成し、同じ評価複体の pinched 模型との全空間比較と実閉後合成への自然性を証明した。元の出力の射影性を仮定せず、加群の準同型による同じ pinched 後合成の全空間同値を証明した。共変・反変の augmentation を空間値の全単体的ホモトピーへ送った。同じ F1 の Yoneda 評価・始点固定 Tw の pointed 表示・全 fiber の同値、元の始点固定 Tw 輸送の同値性から実像の辺の可逆性を導く判定まで構成し、集約ビルド・両公理監査済み。
- 全 Hom の同じ閉後合成の準同型性から元の dg nerve の実 coslice 輸送の同値性を証明し、R の代表加群からの実輸送を介して、同じ基礎空間 ∞ 関手が任意の加群準同型の実辺を反転することを証明した。同じ実 augmentation ホモトピーの頂点辺そのものを元の augmentation の実閉辺へ同定し、実分解圏上の基礎空間値全関手の比較同型と、同じ厳密切断に沿った全実出力関手の比較同型を構成した。元の出力の射影性を仮定しない。共変・dg 反対模型・実反対 ∞ 圏の固定入力 Hom への制限も全関手比較同型として証明した。追加13モジュールも集約ビルド・両公理監査済み。
- 同じ閉射で始点を置換する実 coslice 全体の写像を構成し、全面・退化への自然性と底射影の保存を証明した。Hom(x,x) の同じ単位を dg Yoneda で拡張した実閉射から、元の coslice 全体の比較と同じ空間値 Hom を底とする pointed 表示を構成した。公開済みの半自由 Hom 関手族へ厳密に接続し、同じ実 fiber 射も構成した。全次数の比較鎖写像は同じ dg Yoneda 同型の逆そのもので、鎖同型である。追加9モジュールも集約ビルド・両公理監査済み。実 fiber 射への同じ鎖同型の反映も証明した（次項）。
- 左 Hom と dg 反対模型の右 Hom の同じ全単体同型・全線形座標を構成し、実 coslice fiber の閉前合成と dg 関手像を同じ Hom 鎖写像の作用へ厳密に同定した。合成 Hom 鎖写像の準同型性だけから実合成 fiber 射の同値性を導く判定を証明した。同じ Hom 単位の比較鎖同型を対象宇宙持ち上げ後にも照合し、`dgHomTargetCosliceComparison_fibers_isQCatEquivalence` で構成済みの元の実 coslice 比較の全実 fiber 同値を証明した。入力の小ささや元の出力の射影性は仮定しない。追加13モジュールも集約ビルド・両公理監査済み。持ち上げた pointed 表示の全 fiber 同値と固定始点の全関手比較も次項で完成。
- 同じ実四角形の fiber 射の合成・宇宙持ち上げを照合し、Hom の同じ pointed 表示の全実 fiber 同値を証明した。同じ実 coslice の二つの transport 表現を一つの可縮な表現空間内の証人で比較し、空間値の全関手と pointed 全空間の両方の同型を構成した。半自由加群へ制限し、`dgSemifreeDerivedHomTargetF1SpaceIso` で実 D(R) 値共変 Hom の基礎空間を元の F1 二変数 Hom∞ の固定始点制限へ全関手同型として接続した。反対 dg 圏の左 representable と元の右 representable を全 cochain 上で同定し、底同型に沿う同じ coslice の分類比較と右 slice の反転を接続した。`dgSemifreeDerivedHomContravariantF1SpaceIso` で実反対 ∞ 圏上の D(R) 値反変 Hom を元の `representablePresheafInfinity` へ全関手同型として接続した。二変数の D(R) 値統合は未証明。追加12モジュールは最終集約ビルド・両公理監査済み。
- 任意の `Bimodule R E D` の実 dg tensor を半自由入力へ制限し、同じ実出力分解と対象宇宙の上げ下げから `dgKernelDerivedInfinity` を構成した。D・E は同じ対象宇宙。元の出力の射影性は不要。同じ頂点の半自由値と元の同じ tensor への augmentation、各評価の準同型性・全整数次数の全射性を証明した。元の出力が射影的な場合の同じ augmentation の全関手同型、既存の射影的模型による実導来関手との比較を構成し、一般作用の graph を元の `dgModuleExtensionInfinity` と比較して完全性を回収した。全 Hom 自然な双加群同型を実 nerve の全関手同型へ送り、同じ対角双加群の実導来作用を恒等関手へ比較した。Hom の局所 K-flat 性は仮定しない。通常 tensor の合成の生の nerve 上の全関手比較も証明した。導来化後の一般合成・coherence・一般 Morita 不変性は未証明。追加11モジュールは集約ビルド・両公理監査済み。
- 全 Hom 自然な次数別全射準同型 `a:F→G` に沿い、同じ実入力・半自由出力を保つ実分解変更 dg 関手を構成した。比較差の可換四角形、同じ Hom 鎖写像の二射影・比較 cochain、実単位と全 Hom 合成の保存を証明し、宇宙持ち上げ後の両射影の厳密等式を回収した。元の両入力同値の指定逆を使い、同じ実出力分解 ∞ 関手と元の実半自由出力 ∞ 関手を全関手同型で比較した。入力の Small 性・元の出力の射影性は不要。balanced tensor の斉次生成元から左加群側の全次数全射性の保存を証明し、`dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso` で双加群の次数別全射準同型に沿う元の実導来作用の全関手同型へ接続した。任意の非全射準同型の比較は次項で完成。比較の合成 coherence・一般導来合成は未証明。追加16モジュールは集約ビルド・両公理監査済み。
- 実 disk 被覆の非輪状性と非輪状直和項の第一射影の準同型性から、元の任意の加群準同型を回収する実切断付きの共通 span を構成した。同じ右加群・双加群同値と評価自然同型に沿い、全 Hom 自然な双加群 span へ戻し、両脚の全評価の全整数次数全射性・準同型性、切断との二合成を照合した。`dgKernelDerivedInfinity_mapIso_of_quasiIso` で、全射性を仮定しない元の任意の双加群準同型の実導来作用を全関手同型で比較した。局所 Hom の平坦性・元の tensor 出力の射影性は不要。比較の合成 coherence と一般導来合成は未証明。追加7モジュールは集約ビルド・両公理監査済み。
- 任意の dg 入力前合成 `H:A→C` に沿い、元の replacement・augmentation を保つ実分解 dg 関手を構成した。入力に H.map、半自由出力と比較 cochain に恒等を使い、二射影・入力像・単位・全 Hom 合成・両合成比較項の厳密等式を証明した。対象宇宙持ち上げ後の両射影の厳密等式と同じ入力同値の指定逆から、`dgModuleOutputResolution_precompIso` で出力 ∞ 関手の全関手同型を回収した。入力の Small 性・元の出力の射影性は不要。追加10モジュールは集約ビルド・両公理監査済み。
- Small 性を仮定しない任意の dg 圏 C の局所 Hom から、`dgHomTensorFunctor` を構成した。有限実充満像内の対角双加群を使い、単位・全 Hom 合成・固定入力の二つの厳密制限を証明した。同じ半自由入力上の tensor dg 圏の nerve から実 D(R) 値の出力分解 ∞ 関手を構成し、固定始域・固定終域の既存 D(R) 値 Hom と全関手同型で比較した。同じ頂点の半自由値と元の全 Hom end への全射準同型を回収し、基礎空間の両固定入力制限を元の F1 Hom∞・実反対上の表現可能前層へ全関手同型で比較した。始域を元の二つの nerve の直積へ移す構成は未証明。追加8モジュールは集約ビルド・両公理監査済み。
- 実 dg nerve の二入力 tensor を0・1・2単体で構成した。同じ斉次 tensor の微分・双線形性・閉性と、二つの境界 cochain の tensor 和の微分式から、元の実三角形の三辺と比較 cochain を保つ tensor 三角形を構成した。実二単体の三面は、入力の同じ三面の tensor に厳密に一致する。実一単体の二面と単位退化、実二単体の二つの退化も厳密に保存。原始元の選択や存在命題で代用していない。3次元以上の構成・全次元の自然性は未証明。追加7モジュールは集約ビルド・両公理監査済み。
- 全次元の実切断合成と指定次数の符号付き tensor 有限和を構成した。空・一切断の式、空切断項、各辺の元の二辺の tensor との一致・閉性を証明した。候補は `SimplexData` であり、高次 HA と全次元の自然性は未証明。追加9モジュールは集約ビルド・両公理監査済み。
- 入口：D7 は `Derived/StableTriangulatedEquivalence.lean`、β3 は `DGQuotientLocalization`・`ResolvedDGQuotientVerdierSequence`、β5 は `DGAlgebraDerivedInfinity`・`DGAlgebraPerfectMoritaInfinity`・`DGModuleHomSpaceInfinity`・`DGSemifreeContravariantHomInfinity`・`DGModuleFunctorResolutionCategory`・`DGModuleFunctorResolutionNerve`・`DGModuleOutputResolutionInfinity`・`DGSemifreeDerivedHomValue`・`DGSemifreeDerivedHomMappingSpace`・`DGModuleAugmentationPrismSimplex`・`DGModuleAugmentationPrismReindex`・`DGModuleAugmentationDegenerateReindex`・`DGModuleAugmentationNervePrism`・`DGModuleAugmentationPrismComponent`・`DGModuleOutputResolutionHomotopy`・`DGSemifreeDerivedHomAugmentationInfinity`・`DGModuleUnderlyingSpaceInfinity`・`DGModuleUnitPinchedNaturality`・`DGModuleUnderlyingSpacePointed`・`DGSemifreeHomSpaceAugmentation`・`DGClosedCosliceTransport`・`DGModuleUnderlyingSpaceQuasiIso`・`DGModuleAugmentationUnderlyingIso`・`DGModuleOutputResolutionSpaceIso`・`DGSemifreeHomSpaceComparison`・`DGClosedCoslicePrecomposition`・`DGHomTargetUnitComparison`・`DGHomTargetPointedDisplay`・`DGSemifreeHomTargetPointedDisplay`・`DGLeftPinchedChainMap`・`DGClosedCosliceFiberComparison`・`DGFunctorClosedCosliceComparison`・`DGHomTargetCosliceFiberEquivalence`・`DGHomTargetSpaceComparison`・`DGSemifreeHomTargetSpaceComparison`・`DGSemifreeHomSourceSpaceComparison`・`DGKernelDerivedInfinity`・`DGKernelDerivedValue`・`DGKernelGraphComparison`・`DGKernelIdentityInfinity`・`DGKernelTensorComposition`・`DGModuleResolutionChangeFunctor`・`DGModuleResolutionChangeInfinity`・`DGModuleResolvedChangeComparison`・`DGKernelComparisonInfinity`・`DGBimoduleQuasiIsoSurjectiveSpan`・`DGKernelQuasiIsoComparison`・`DGModuleResolutionPrecompFunctor`・`DGModuleOutputResolutionPrecomp`・`DGHomTensorFunctor`・`DGHomTensorRestrictions`・`DGSemifreeHomTensorInfinity`・`DGSemifreeHomTensorComparison`・`DGSemifreeHomTensorValue`・`DGSemifreeHomTensorSpaceComparison`・`DGTensorElementCalculus`・`DGTensorBoundary`・`DGTensorTriangleData`・`DGTensorLowSimplex`・`DGTensorTwoDegeneracy`・`DGNerveListCutProduct`・`DGNerveListCutLow`・`DGNerveCutProduct`・`DGNerveListCutStep`・`DGTensorElementHEq`・`DGNerveTensorCutTerm`・`DGNerveTensorCandidate`・`DGNerveTensorEmptyCut`・`DGNerveTensorEdge`（すべて `Derived/`）。

### 残り（依存順、時間は推定）

- β3 完了（2026-10-21）：局所 K-flat 商と平坦分解後の商の全局所化、全零化完全関手 ∞ 圏の普遍性、実安定閉包の包含を左項とする Verdier 列まで証明・監査済み。次は β5。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b の提供済み lax pullback を読み取り専用で使う。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`・`suspensionEquivalence`・`pretriangulated_ho`・`isTriangulated_ho`・`exactFunctor_isTriangulated`。
- `cofiberBoundaryLiftQ_differential`・`cofiberBoundaryLiftA_differential`・`standardCofiberCocone_isColimit`・`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyEquivalenceCommShift`・`derivedStableHomotopyEquivalenceIsTriangulated`。
- `dgModuleNerve_isStable`・`dgRoofCorrespondenceMap`・`dgRoofCorrespondenceFiberIso`・`dgQuotientRoofCorrespondenceProjection_leftFibration`。
- `dgQuotientFixedHomRoofMap_isRightCofinal`・`dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_piZero_surjective`。
- `dgGeneralLastHornTopResidual_differential`・`dgGeneralLastHornConeResidual_closed`・`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary`。
- `dgVerdierTruncatedConeSuccessor_nonempty`・`dgVerdierTruncatedConeData_nonempty`。
- `dgVerdierFiniteJoinCone_nonempty`・`finiteSimplicialOpposite`・`dgVerdierOver_op_isFilteredInfinity`。
- `dgActualRoofFiberReduction_nonempty`・`dgActualRoofClosedCoefficient_square`・`dgActualRoofReducedFiller_exists`。
- `roofRelativeCompositionTriangle_exists`・`roofCompatibleTransportComposite_nonempty`・`RoofCompatibleTransportComposite.boundary`。
- `RoofHomotopyRelativeFiller`・`dgActualRoofHomotopyRelativeFiller_nonempty`。
- `dgQuotientFinite_exists_coefficientFillers`・`dgCoefficientSkeletalStep_nonempty`・`finiteRelativeSkeleton_exists_top`。
- `dgCoefficientSkeletalStage_nonempty`・`dgCoefficientFinitePairs_nonempty`・`dgClosedRoofFinitePairs_nonempty`・`dgActualRoofFinitePairs_nonempty`。
- `HasFiniteHomotopyRelativeFillers.isLeftCofinal`・`isWeaklyContractible_of_finiteNullSpans`。
- `dgRoofCorrespondenceMap_isLeftCofinal`・`dgRoofCorrespondenceMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_precompose_kan`。
- `dgInvertingFixedHomRoofMap_isRightCofinal`・`dgInvertingHomDescent_nonempty`・`DGInvertingHomDescent.homMap_restriction`。
- `dgInvertingHomMap_postcomp`・`dgInvertingHomDescentSpace_isContractibleKan`・`dgInvertingHomActionFamilyRestrictionIso`。
- `dgActualRoofVertexSpan_rightInverse`・`dgActualRoofComposition_nonempty`・`actualRoofEvaluation_compositionTriangle_nonempty`。
- `dgActualRoofEvaluationTargetEdge`・`dgQuotientHomFinite_actualRoofLift`・`dgInvertingHomActionFamilyRoofEvaluationIso`。
- `dgFiniteHomotopyDescent_nonempty`・`pinchedClosedPostcomposition_precomposition`・`dgFiniteOreRefinement_nonempty`・`dgFiniteRoofPresentation_nonempty`・`dgFiniteRoofOreData_nonempty`・`pinchedHomCompositionFamily_assoc`・`DGFiniteRoofOreData.compositeDiagram_projection`・`pinchedHomCompositionFamily_closed_post`・`pinchedHomCompositionHomotopy_fixed`・`DGFiniteOreRefinement.compositionHomotopy_h`。
- `dgCoherentHomComparison_slice`・`dgPinchedCompositionPrism_projection`・`dgPinchedCompositionFamilyPrism_precomp`。
- `homotopyCompositionRelativeOver_fixedLeft_exists`・`dgFiniteOreTrianglePrisms_relative_exists`・`dgFiniteRoofCompositionPrisms_exists`。
- `roofLeftFibration_terminalEvaluation_nonempty`・`dgInvertingHomActionFamilyEvaluationIso`・`dgInvertingHomFamilyEvaluation_nonempty`。
- `pinchedFamilyHom_eq_iff_homotopy`・`dgInvertingFamilyDenominator_isIso`・`dgInvertingFiniteRoofComposition_nonempty`・`dgFiniteRoofOreDataPrecomp_compositeDiagram`。
- `dgNerveOppositeIso`・`dgNerveOppositeIso_naturality`・`dgSemifreeContravariantHomInfinity`・`dgModuleFunctorResolutionHomComplex`・`dgModuleFunctorResolutionHom_ext`・`dgModuleFunctorResolutionSourceHomMap_quasiIso`・`complexMappingCoconeMap`・`complexShortExact_quasiIso_projection`・`dgModuleHomSpaceInfinity`・`dgModuleHomSpaceValueEquivalence`・`dgSemifreeHomTargetInfinity`・`dgSemifreeHomSourceInfinity`・`dgMoritaAdjunctionInfinity`・`dgPerfectMoritaRightAdjointInclusionIso`・`dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita`・`dgPerfectExtensionInclusionIso`・`dgAlgebraPerfectInfinityCategory_isStable`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_morita`・`dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso`・`dgModuleDerivedFunctor_isQCatEquivalence_of_classical`・`dgAlgebraExtensionInfinity_isExactFunctor`・`dgModuleDerivedFunctor_comparisonIso`・`dgModuleDerivedFunctor_id_iso`・`dgModuleDerivedFunctor_comp_iso`・`dgAlgebraDerivedInfinityCategory_isStable`・`dgModuleDerivedInfinityCategory_isStable`・`dgSemifreeToProjectiveNerve_isQCatEquivalence`・`dgQuotientNerveProjection_isLocalization`・`dgVerdierExactPrecomposition_isQCatEquivalence`・`dgStableClosureNerve_isStable`・`dgStableClosureInclusion_isExactFunctor`・`dgQuotient_isStableVerdierSequence`・`resolvedDGQuotientFunctor_isLocalization`・`resolvedDGVerdierExactPrecomposition_isQCatEquivalence`・`resolvedDGQuotient_isStableVerdierSequence`。

### 依存と提供

- Core・F1・F1B・F2・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。
- **Sp から D への判定補題要求（2026-10-21、未提供）**：[HA Cor. 1.4.2.27](https://www.math.ias.edu/~lurie/papers/HA.pdf) の (3) ⇒ (1) を F3 の定義で使いたい。正確な要求は、`X : SSet.{u}`、`[Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]`、実関手 `s : X ⟶ loopDiagrams X`、`hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X`、`hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)` から `IsStable X` を得る一般補題。s は実際の普遍 loop 四角形の全単体族であり、安定性を先取りする既存 loopFunctor の使用は避ける。有限余極限・cofiber の存在と任意 ZeroTriangle の fiber/cofiber 同値を結論として証明し、それらを追加仮定にしない。現存の isStable_of_finite_limits_colimits は有限余極限と全四角形の双カルテジアン判定も要求するので代用できない。Sp が自前で証明する場合は Spectra 配下に置き、Stable/ は編集せず後で D が取り込む。Sp への適用には有限極限の包装と実 loop 関手の同値性がなお必要で、要求の記載を証明済みとは数えない。

### 未コミット

- なし。今回の9モジュール（切断合成・全次元 tensor 成分候補・辺の比較）と集約・両監査・本計画を保存した。高次 HA 方程式・面と退化への自然性は未証明。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルド成功（9649 jobs）。公理監査は Derived 13586 宣言／1533 モジュール、Stable 14701／1803。許容三公理のみ。今回までの保存対象464新規モジュールは警告なし。Hom 降下・実合成・全選択空間の評価比較の主経路に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零化・平坦模型との比較、前三角性の cell 分解への反映、平坦分解後の商の実安定性と商関手の完全性は完成。局所 K-flat 商の全 ∞ 関手圏の局所化普遍性は完成。零化完全関手圏の普遍性・実安定閉包の Verdier 列まで完成。平坦分解後の元の Hom の平坦性を仮定しない局所化・全零化完全関手 ∞ 圏の同値・Verdier 列も統合・監査完了。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β5：全次元の実切断合成 cochain と符号付き有限和 `dgNerveTensorDataCandidate` を構成した。切断点を昇順列に移し、先頭で区切る再帰を使う。指定次数 `2-|I|+|S|`、停止性、一段の再帰式、空・一切断の式、空切断の tensor 項、各辺が同じ二辺の tensor であることと閉性を証明済み。次は草稿 `/tmp/d-beta5-tensor-triangle-calibration.lean` を正式化する（補助補題・一切断項・三頂点の有限和と既存 `dgTensorTriangle` の cochain の一致・同じ三角形の HA 微分式、4宣言、単独 Lean 検査済み。未統合・未公理監査で提供数に含めない）。次に3次元の実 HA 方程式で交差符号（左切断点 < 右非切断点）を照合する。続いて全次元の Leibniz 展開・削除と切断の項の相殺、全面・退化への自然性、固定入力包含への制限を証明する。候補は `SimplexData` であり、全 HA を満たす `Simplex` や直積から tensor nerve への写像とはまだ主張しない。再帰全体の simp 展開はループするので `dgNerveListCutProduct_cons` と `dgNerveListCutStep` を使う。
- 続いて二変数の D(R) 値 Hom を統合する。実 Hom を対象とし、両入力の全単体に整合する作用を構成する。`DGTensorCategory` の nerve を元の二変数の直積と無条件に同一視しない。各固定入力の既存出力分解の比較を全二変数族へ移し、構成済みの両側の全関手同型と照合する。
- 固定始点では同じ分類証人が底の全関手と pointed 全空間の両方を比較する。反変側は同じ全 cochain の符号一致・`dgNerveOppositeIso`・同じ実 coslice の底同型・右 slice の反転から元の F1 表現可能前層へ比較した。二変数の D(R) 値統合・一般 tensor–Hom 随伴は未証明。全加群の生の dg nerve で augmentation が同値とは限らないので、元の出力の射影性やその可逆性を仮定しない。必要な比較は実導来化後に行う。
- その後一般 tensor–Hom 随伴・全 coherence、一般双加群作用の準同型・導来合成と Morita 不変性、Perf の冪等完備性を閉じて β4 へ進む。β4 は提供済み F2 の実 lax pullback を読み取り専用で使う。β3 は局所化・Verdier 列とも完了しており、再実装や承認待ちは不要。

作成日：2026-10-18。状態：S1〜S7（D7）・β3 完了。β5 に進む。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/StableTriangulatedEquivalence.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定、IsStable、実 suspension 由来の全整数シフト、標準 cofiber 三角形の像の同型、全 distinguished triangle の保存・反映、単位・余単位と整合する三角同値 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f を既提供とせず、S7 の coslice の直接充填で標準 cofiber の押し出し性を証明した。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。


## β3：Drinfeld 商と ∞ 圏的 Verdier 商

D7 の後に完了。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda 模型との同値、前三角 dg 圏と平坦分解後の商の実 dg nerve の安定性、商関手の完全性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、局所 K-flat な場合は同じ宇宙の任意 quasicategory 標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明済み。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏の平坦分解後の商の実安定性と商関手の完全性は完成。
  局所 K-flat 商と平坦分解後の商の零化完全関手 ∞ 圏の同値・実安定閉包の Verdier 列まで完成・監査済み。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

着手済み。非可換 `Mon (Complex R)` の D(A)・Perf(A) の実安定性、graph tensor・Morita 不変性、実二変数 Hom 空間、固定入力ごとの D(R) 値共変・反変 Hom と実全 Hom 複体への augmentation・各対の全写像空間比較まで完成。共変・反変の各固定入力の空間値全関手は元の F1 Hom∞ との同型まで完成。任意双加群の実作用、graph 比較と対角単位、次数別全射準同型に沿う全関手比較も構成した。二変数の D(R) 値統合・一般 RHom 随伴は未完。L4 §26 の dg 圏分解と dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、提供済みの α2b の Cat_∞ の極限・安定な lax pullback に接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
