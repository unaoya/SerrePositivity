module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectIdempotentCompleteGeneral
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedTria
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
/-!
概要：前三角な小 dg 圏の実 Yoneda は、実 Perf への native 冪等完備化を与える。
方針：perfect 加群を有限 cell の retract と表示し、前三角性で有限 cell を同じ Yoneda 像へ戻す。
規約：全 Perf の Small 性や S 構成固有の入力を要求しない。既存宣言は変更しない。
使われ方：D-21 の Thomason 判定と、実 Drinfeld 商から Perf への完備化の特殊化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

abbrev dgPerfectDerivedHoComparison :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (PerfectDGModule R D)).functor ⋙
    _root_.SerrePositivity.DifferentialGraded.perfectDGModuleToDerived R D Set.univ

def dgPerfectVertex_classicalIso (M : _root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) :
    (dgPerfectDerivedHoComparison R D).obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) ≅
        (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val) :=
  (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app _

lemma dgPerfectVertex_retract_yoneda [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]
    (M : _root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) : ∃ x : D,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R D).obj x)) := by
  obtain ⟨N, hN, ⟨r⟩⟩ := (_root_.SerrePositivity.DifferentialGraded.modulePerfectOver_iff R D Set.univ _).mp M.property.2
  let Z : TriaCategory R D := ⟨(_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N,
    (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver R D Set.univ).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D) hN⟩
  obtain ⟨x, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable R D Z
  let H := dgPerfectDerivedHoComparison R D
  let s := (Retract.ofIso (dgPerfectVertex_classicalIso R D M)).trans
    (r.trans ((Retract.ofIso ((_root_.SerrePositivity.DifferentialGraded.triaInclusion R D).mapIso e)).trans
      (Retract.ofIso (dgPerfectVertex_classicalIso R D ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R D).obj x)).symm)))
  refine ⟨x, ⟨⟨H.preimage s.i, H.preimage s.r, ?_⟩⟩⟩
  apply H.map_injective
  rw [H.map_comp, H.map_preimage, H.map_preimage, s.retract, H.map_id]

lemma dgPerfectYonedaInfinity_isIdempotentCompletion [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R D) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleNerve_isIdempotentComplete R D,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isFullyFaithful R D, ?_⟩
  intro z
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  obtain ⟨x, hx⟩ := dgPerfectVertex_retract_yoneda R D M
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u+1) v} R D).obj x), ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaCommonFunctor R D)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex _))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact hx

end SerrePositivity.InfinityCategories.Project.DerivedCategories
