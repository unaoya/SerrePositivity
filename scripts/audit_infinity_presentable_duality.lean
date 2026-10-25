import SerrePositivity.InfinityCategories.F2.Presentable.Duality.All
import Lean.Util.CollectAxioms

/-!
概要：P-d の所有する全宣言の再帰的公理依存を監査する。
方針：Duality 名前空間のモジュールから導入された宣言を列挙する。
規約：propext・Classical.choice・Quot.sound だけを許す。
使われ方：Duality.All のビルド後の独立監査。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.InfinityCategories.F2.Presentable.Duality).isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Presentable duality: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Presentable duality: no declarations audited"
  logInfo m!"Presentable duality audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftVertex_exists_rightAdjoint
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightVertex_exists_leftAdjoint
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightAdjoint_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftAdjoint_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftRoundtripIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightRoundtripIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightIdentityIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftIdentityIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenRightCompositeIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.chosenLeftCompositeIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightMateIntervalMap
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightMateIntervalMap_family
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionHomEquiv
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionMap_transpose_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.AdjointUnitMappingSpace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_surjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_surjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitAdjunction_unitHom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_isEssentiallySurjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_isEssentiallySurjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rawAdjointUnitSpace_kanComplex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rawAdjointUnitSpace_projection_fibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitCoreIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_innerFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_innerFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeftFiber_kanComplex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiber_kanComplex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUniversalUnitSpace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUniversalUnitSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.unitComposition_fixedRight
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitCosliceComparison_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiberToCoslice
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiberToCoslice_unit
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiberToCoslice_left
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiberToCore_ι
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.qcatAdjunctionChangeLeft
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.qcatAdjunctionChangeRight
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.qcatAdjunctionChangeLeft_unitHom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.qcatAdjunctionChangeRight_unitHom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.cosliceUnit_homMk_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitHom_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitCondition_of_vertexIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitVertex_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.cosliceCommaComparison_fiberArrow_edge
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.postcompositionUnit_identity_component
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitVertex_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnit_condition_iff_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightAdjointUnitSubspace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightAdjointUnitSpace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitSubspace_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightFiberComparison_unitCondition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightFiberToAdjointUnitSpace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitLeft_preservesSmallColimits
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitLeft_ι
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitRaw
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitReturn
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitReturn_right
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointUnitToFiber
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightUnitFiberIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightFiber_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.internalHomComposition_tensorEdge_hom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rawUnitCondition_of_edge
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rawUnitCondition_of_vertexIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitFullSpace_fibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_fibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_fibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightMappingEquivalence

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionUnitEdge
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionUnitHom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeHomEquiv_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeHomEquiv_pre_right
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeHomEquiv_pre_left
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneSymm_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneSymm_precomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneSymm_whiskerRight

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_precomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_postcomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.functorHomCongr_refl
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.functorHomCongr_source_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.functorHomCongr_trans
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.functorHomCongr_postcomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_congr

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeHomMap
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.homSourceTransportPackage
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.sourceHomTransportEquiv_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.sourceHomTransportEquiv_factor
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.sourceHomTransportEquiv_eq_congr
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionSourceEquiv
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTargetEquiv
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTransposeEquiv_formula
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTransposeEquiv_comp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTransposeEquiv_precomp
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTransposeEquiv_parameter
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionCorrespondence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.LeftUnitComma
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitComma_hasInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUniversalUnitSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.unitComposition_fixedLeft
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitCosliceComparison_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitCoslice_hasInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeftFiberToCoslice

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_formula
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointHomOneEquiv_identity
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeIdentity_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposePre_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.transposeHomEquiv_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionTargetEquiv_unit_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionSourceEquiv_unit_evaluate
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.precompositionAdjunction_unitComponent_identity

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitVertex_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitVertex_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnit_condition_iff_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointUnitSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointUnitRight_condition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftFiberToAdjointUnitSpace
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointUnitToFiber
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftUnitFiberIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeftFiber_isContractibleKan
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeftMappingEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointMappingEquivalence

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeft_extend
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRight_extend
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitLeftSection_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointUnitRightSection_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointMappingFamily_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointMappingFamily_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.rightAdjointMappingFamilyAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.leftAdjointMappingFamilyAdjunction

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairDiagram_pre
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLift
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftLeft
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftRight
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedZeroIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairUnitVertex_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointCorrespondence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointLeft
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointRight
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointVertexAdjunction

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.adjointTransformationEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.covariantPairUnitProjection_leftFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomBifunctor
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomFamily
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftVertex_left
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftVertex_right
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.twistedPairLiftVertex_unit
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointVertex

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointLeft_surjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairAdjointRight_surjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairFixedLeftBase_composition
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomFamily_vertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairFixedLeftCosliceIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairFixedLeftCosliceIso_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomAtLeft_cosliceIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.fullLeftUnitRepresentationIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomAtLeft_representationIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairCovariantYoneda_isFullyFaithful
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomFamily_in_covariantYonedaImage
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor_ulift
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctorLifted_yonedaIso

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairCompositeFunctorIsoVertex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairCovariantYonedaPreimageVertexIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor_vertexIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor_isEssentiallySurjective
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointValueIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctorAdjunction
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomAtRight_representationIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.initialVertex_pullback_fullSubcomplex
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.preservingLeftUnitVertex_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.preservingRightUnitVertex_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitRelativeEvaluation_trivialKanFibration
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitPointHomFamily_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairClassifierPointedDisplayFiber_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairLeftUnitPointedDisplay_projection
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightUnitPointedDisplay_projection

#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairLeftUnitPointedDisplayFiber_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightUnitPointedDisplayFiber_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitPointedDisplay_vertex_eq
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairLeftUnitUnstraighteningMap_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitUnstraighteningVertex_isInitial
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairTransformationEvaluation_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairTransformationEvaluation_parametrizedIso
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairCanonicalUnitPoint_eq_rightDisplay
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomFamily_evaluate_right
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitEvaluatedTransport_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairUnitHomFamily_isFullyFaithful
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor_isFullyFaithful
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.pairRightAdjointFunctor_isQCatEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.presentableAdjointFunctorEquivalence
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.presentableAdjointFunctorEquivalence_hom
#check @SerrePositivity.InfinityCategories.F2.Presentable.Duality.presentableAdjointFunctorEquivalence_adjunction
