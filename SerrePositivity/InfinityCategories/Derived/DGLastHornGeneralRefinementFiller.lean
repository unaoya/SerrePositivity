module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralRefinedResiduals
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralPrimitiveEquations
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralConePrimitive

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

variable {n : ℕ}
variable [Small.{u} D] {P : Set D}
variable {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D}
variable (H : DGGeneralLastHornResidualRefinement P σ)

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 Q。 -/
def DGGeneralLastHornResidualRefinement.refinedQ :
    GradedHom A ((HornData.knownData (dgGeneralLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgGeneralLastHornSourceRefinement σ H.q H.s)).obj
        (dgLastHornPenultimate n)) (-(n : ℤ)) :=
  gradedHomTransport (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s).symm
    (dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s).symm rfl H.Q

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 A。 -/
def DGGeneralLastHornResidualRefinement.refinedA :
    GradedHom A ((HornData.knownData (dgGeneralLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgGeneralLastHornSourceRefinement σ H.q H.s)).obj
        (Fin.last (n + 2))) (-(n : ℤ) - 1) :=
  gradedHomTransport (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s).symm
    (dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s).symm rfl H.a

/-- 型だけを移した Q は元の回収 Q と一致する。 -/
lemma DGGeneralLastHornResidualRefinement.refinedQ_heq : HEq H.refinedQ H.Q :=
  gradedHomTransport_heq _ _ _ _

/-- 型だけを移した A は元の回収 A と一致する。 -/
lemma DGGeneralLastHornResidualRefinement.refinedA_heq : HEq H.refinedA H.a :=
  gradedHomTransport_heq _ _ _ _

/-- 回収した Q は、貼った新ホーンの欠けた面の微分式を満たす。 -/
lemma DGGeneralLastHornResidualRefinement.refinedQ_differential :
    differential A H.refinedQ = dgGeneralLastHornMissingResidual
      (dgGeneralLastHornSourceRefinement σ H.q H.s) := by
  have hd := gradedHom_differential_heq (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s) rfl H.refinedQ H.Q H.refinedQ_heq
  have hq : differential A H.Q =
      dgGradedPrecompose A D (-(n : ℤ) + 1) (dgGeneralLastHornMissingResidual σ) H.s :=
    H.Q_differential
  exact eq_of_heq ((hd.trans (heq_of_eq hq)).trans
    (dgGeneralLastHornSourceRefinement_missingResidual σ H.q H.s).symm)

/-- 回収した A は、貼った新ホーンの同じ Q と最上位微分式を満たす。 -/
lemma DGGeneralLastHornResidualRefinement.refinedA_differential :
    differential A H.refinedA =
      dgGeneralLastHornTopResidual (dgGeneralLastHornSourceRefinement σ H.q H.s) +
      compose A ((HornData.knownData (dgGeneralLastHornSourceRefinement σ H.q H.s)).edgeHom
        (dgLastHornPenultimate n) (Fin.last (n + 2))
          (dgLastHornPenultimate_lt_last n)) H.refinedQ (by omega) := by
  have hd := gradedHom_differential_heq (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl H.refinedA H.a H.refinedA_heq
  have hc := gradedHom_compose_heq (k := -(n : ℤ) - 1 + 1) (k' := -(n : ℤ) - 1 + 1)
    (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (dgGeneralLastHornSourceRefinement_obj_penultimate σ H.q H.s)
    (dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl rfl rfl _ _ _ _
    (dgGeneralLastHornSourceRefinement_lastEdge σ H.q H.s) H.refinedQ_heq (by omega) (by omega)
  have hr := gradedHom_add_heq (dgGeneralLastHornSourceRefinement_obj_zero σ H.q H.s)
    (dgGeneralLastHornSourceRefinement_obj_last σ H.q H.s) rfl _ _ _ _
    (dgGeneralLastHornSourceRefinement_topResidual σ H.q H.s) hc
  have ha : differential A H.a =
      dgGradedPrecompose A D (-(n : ℤ) - 1 + 1) (dgGeneralLastHornTopResidual σ) H.s +
      compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n) (Fin.last (n + 2))
          (dgLastHornPenultimate_lt_last n)) H.Q (by omega) :=
    H.a_differential_original
  exact eq_of_heq ((hd.trans (heq_of_eq ha)).trans hr.symm)

/-- 原始元の同じ実 Q・A は、細分した実ホーンの型付き二未知解を与える。 -/
def DGGeneralLastHornResidualRefinement.solution :
    DGGeneralLastHornSolution (dgGeneralLastHornSourceRefinement σ H.q H.s) :=
  dgGeneralLastHornSolutionOfCochains H.refinedQ H.refinedQ_differential
    H.refinedA H.refinedA_differential

/-- 細分ホーンの充填は元の指定終端面を厳密に保つ。 -/
lemma dgGeneralLastHornSourceRefinement_filler_face0
    (F : Δ[n + 2] ⟶ dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = dgGeneralLastHornSourceRefinement σ H.q H.s) :
    SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F = horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ σ := by
  rw [← horn.ι_ι_assoc (Fin.last (n + 2)) 0 (by simp), hF,
    dgGeneralLastHornSourceRefinement_preserves_face_zero]

/-- 最後辺が実分母の実ホーンは、追加実閉分母後に全体を実際に充填できる。 -/
theorem dgGeneralLastHorn_exists_sourceRefinement_filler [IsDGPretriangulated A D]
    (P : Set D) (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)
    (hW : (dgClosedEdge A D (dgGeneralLastHornFinalClosed σ)).edge ∈ dgVerdierEdges A D P) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
        ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0)),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∃ F : Δ[n + 2] ⟶ dgNerve A D,
          (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = dgGeneralLastHornSourceRefinement σ q s := by
  obtain ⟨H⟩ := dgGeneralLastHornResidualRefinement_nonempty P σ hW
  exact ⟨H.q, H.s, H.denominator, H.solution.extension, H.solution.fac⟩

end SerrePositivity.InfinityCategories
