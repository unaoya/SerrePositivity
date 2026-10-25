module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Derived.DGPerfectIdempotentCompleteGeneral
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedTria
public import SerrePositivity.InfinityCategories.F2.Idempotent.Completion
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

abbrev dgPerfectDerivedHoComparison :=
  (dgStableHomotopyEquivalence R (PerfectDGModule R D)).functor ⋙
    perfectDGModuleToDerived R D Set.univ

def dgPerfectVertex_classicalIso (M : PerfectDGModule R D) :
    (dgPerfectDerivedHoComparison R D).obj
      (SSet.HomotopyCategory.mk (Simplex.vertex M)) ≅
        (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) M.val) :=
  (moduleToHomotopyDerivedIso R D).app _

lemma dgPerfectVertex_retract_yoneda [IsDGPretriangulated R D]
    (M : PerfectDGModule R D) : ∃ x : D,
    F2.Idempotent.IsVertexRetractOf (X := dgModulePerfectInfinityCategory R D)
      (Simplex.vertex M) (Simplex.vertex ((dgPerfectYoneda R D).obj x)) := by
  obtain ⟨N, hN, ⟨r⟩⟩ := (modulePerfectOver_iff R D Set.univ _).mp M.property.2
  let Z : TriaCategory R D := ⟨(moduleToDerived R D).obj N,
    (moduleFiniteCellOver R D Set.univ).prop_map_obj (moduleToDerived R D) hN⟩
  obtain ⟨x, ⟨e⟩⟩ := dgTria_isRepresentable R D Z
  let H := dgPerfectDerivedHoComparison R D
  let s := (Retract.ofIso (dgPerfectVertex_classicalIso R D M)).trans
    (r.trans ((Retract.ofIso ((triaInclusion R D).mapIso e)).trans
      (Retract.ofIso (dgPerfectVertex_classicalIso R D ((dgPerfectYoneda R D).obj x)).symm)))
  refine ⟨x, ⟨⟨H.preimage s.i, H.preimage s.r, ?_⟩⟩⟩
  apply H.map_injective
  rw [H.map_comp, H.map_preimage, H.map_preimage, s.retract, H.map_id]

lemma dgPerfectYonedaInfinity_isIdempotentCompletion [IsDGPretriangulated R D] :
    F2.Idempotent.IsIdempotentCompletion (dgPerfectYonedaInfinity R D) := by
  refine ⟨dgPerfectModuleNerve_isIdempotentComplete R D,
    dgPerfectYonedaInfinity_isFullyFaithful R D, ?_⟩
  intro z
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  obtain ⟨x, hx⟩ := dgPerfectVertex_retract_yoneda R D M
  refine ⟨Simplex.vertex ((dgUniverseLiftUp.{u, v, max (u+1) v} R D).obj x), ?_⟩
  change F2.Idempotent.IsVertexRetractOf _
    ((dgNerve.map (dgPerfectYonedaCommonFunctor R D)).app _ (Simplex.vertex _))
  rw [dgFunctorNerve_vertex]
  exact hx

end SerrePositivity.InfinityCategories
