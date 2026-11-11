module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralRefinedResiduals
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralPrimitiveEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralConePrimitive

/-! # 追加実閉分母後の指定一般最後外ホーンの実充填

概要：既供給の原始元から回収した Q・A を新対象族へ移し、細分した実ホーン全体を充填する。
方針：新旧対象の等式と cochain の異種等号で二微分式を輸送し、既存の実充填へ渡す。
規約：元の終端面を厳密に保つ。使われ方：実分母図式の二単体上の整合性の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

variable {n : ℕ}
variable [Small.{u} D] {P : Set D}
variable {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
variable (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornResidualRefinement P σ)

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 Q。 -/
def DGGeneralLastHornResidualRefinement.refinedQ :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s)).obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s).symm rfl H.Q

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 A。 -/
def DGGeneralLastHornResidualRefinement.refinedA :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s)).obj
        (Fin.last (n + 2))) (-(n : ℤ) - 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s).symm rfl H.a

/-- 型だけを移した Q は元の回収 Q と一致する。 -/
lemma DGGeneralLastHornResidualRefinement.refinedQ_heq : HEq H.refinedQ H.Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

/-- 型だけを移した A は元の回収 A と一致する。 -/
lemma DGGeneralLastHornResidualRefinement.refinedA_heq : HEq H.refinedA H.a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

/-- 回収した Q は、貼った新ホーンの欠けた面の微分式を満たす。 -/
lemma DGGeneralLastHornResidualRefinement.refinedQ_differential :
    differential A H.refinedQ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s) rfl H.refinedQ H.Q H.refinedQ_heq
  have hq : _root_.SerrePositivity.DifferentialGraded.differential A H.Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ) H.s :=
    H.Q_differential
  exact eq_of_heq ((hd.trans (heq_of_eq hq)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_missingResidual σ H.q H.s).symm)

/-- 回収した A は、貼った新ホーンの同じ Q と最上位微分式を満たす。 -/
lemma DGGeneralLastHornResidualRefinement.refinedA_differential :
    _root_.SerrePositivity.DifferentialGraded.differential A H.refinedA =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s) +
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s)).edgeHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) H.refinedQ (by omega) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl H.refinedA H.a H.refinedA_heq
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (k := -(n : ℤ) - 1 + 1) (k' := -(n : ℤ) - 1 + 1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl rfl rfl _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_lastEdge σ H.q H.s) H.refinedQ_heq (by omega) (by omega)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_topResidual σ H.q H.s) hc
  have ha : _root_.SerrePositivity.DifferentialGraded.differential A H.a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ) H.s +
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n) (Fin.last (n + 2))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) H.Q (by omega) :=
    H.a_differential_original
  exact eq_of_heq ((hd.trans (heq_of_eq ha)).trans hr.symm)

/-- 原始元の同じ実 Q・A は、細分した実ホーンの型付き二未知解を与える。 -/
def DGGeneralLastHornResidualRefinement.solution :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSolutionOfCochains H.refinedQ H.refinedQ_differential
    H.refinedA H.refinedA_differential

/-- 細分ホーンの充填は元の指定終端面を厳密に保つ。 -/
lemma dgGeneralLastHornSourceRefinement_filler_face0
    (F : Δ[n + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ H.q H.s) :
    SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ σ := by
  rw [← horn.ι_ι_assoc (Fin.last (n + 2)) 0 (by simp), hF,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_preserves_face_zero]

/-- 最後辺が実分母の実ホーンは、追加実閉分母後に全体を実際に充填できる。 -/
theorem dgGeneralLastHorn_exists_sourceRefinement_filler [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hW : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornFinalClosed σ)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
        ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∃ F : Δ[n + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D,
          (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornResidualRefinement_nonempty P σ hW
  exact ⟨H.q, H.s, H.denominator, H.solution.extension, H.solution.fac⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
