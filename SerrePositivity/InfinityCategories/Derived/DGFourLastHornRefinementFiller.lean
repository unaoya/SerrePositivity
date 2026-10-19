module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinedResiduals
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinedCochains
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinementFiller
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornSolution

/-! # 追加実閉分母後の指定四次最後外ホーンの実充填

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

variable [Small.{u} D] {P : Set D}
variable {σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D}
variable (H : DGFourLastHornResidualRefinement P σ)

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 Q。 -/
def DGFourLastHornResidualRefinement.refinedQ :
    GradedHom A ((HornData.knownData (dgFourLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgFourLastHornSourceRefinement σ H.q H.s)).obj 3) (-2) :=
  dgGradedHomTransport (dgFourLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (dgFourLastHornSourceRefinement_obj3 σ H.q H.s).symm (-2) H.Q

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 A。 -/
def DGFourLastHornResidualRefinement.refinedA :
    GradedHom A ((HornData.knownData (dgFourLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgFourLastHornSourceRefinement σ H.q H.s)).obj 4) (-3) :=
  dgGradedHomTransport (dgFourLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (dgFourLastHornSourceRefinement_obj4 σ H.q H.s).symm (-3) H.a

/-- 型だけを移した Q は元の回収 Q と一致する。 -/
lemma DGFourLastHornResidualRefinement.refinedQ_heq : HEq H.refinedQ H.Q :=
  dgGradedHomTransport_heq _ _ _ _

/-- 型だけを移した A は元の回収 A と一致する。 -/
lemma DGFourLastHornResidualRefinement.refinedA_heq : HEq H.refinedA H.a :=
  dgGradedHomTransport_heq _ _ _ _

/-- 回収した Q は、貼った新ホーンの欠けた三次面の微分式を満たす。 -/
lemma DGFourLastHornResidualRefinement.refinedQ_differential :
    differential A H.refinedQ = dgFourLastHornMissingResidual
      (dgFourLastHornSourceRefinement σ H.q H.s) := by
  have hd := gradedHom_differential_heq (dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgFourLastHornSourceRefinement_obj3 σ H.q H.s) rfl H.refinedQ H.Q H.refinedQ_heq
  have hq : differential A H.Q =
      dgGradedPrecompose A D (-2 + 1) (dgFourLastHornMissingResidual σ) H.s :=
    H.Q_differential
  exact eq_of_heq ((hd.trans (heq_of_eq hq)).trans
    (dgFourLastHornSourceRefinement_missingResidual σ H.q H.s).symm)

/-- 回収した A は、貼った新ホーンの同じ Q と最上位微分式を満たす。 -/
lemma DGFourLastHornResidualRefinement.refinedA_differential :
    differential A H.refinedA =
      dgFourLastHornTopResidual (dgFourLastHornSourceRefinement σ H.q H.s) +
      compose A ((HornData.knownData (dgFourLastHornSourceRefinement σ H.q H.s)).edgeHom
        3 4 (by decide)) H.refinedQ (by decide) := by
  have hd := gradedHom_differential_heq (dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl H.refinedA H.a H.refinedA_heq
  have hc := gradedHom_compose_heq (k := -2) (k' := -2)
    (dgFourLastHornSourceRefinement_obj0 σ H.q H.s) (dgFourLastHornSourceRefinement_obj3 σ H.q H.s)
    (dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl rfl rfl _ _ _ _
    (dgFourLastHornSourceRefinement_lastEdge σ H.q H.s) H.refinedQ_heq (by decide) (by decide)
  have hr := gradedHom_add_heq (dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl _ _ _ _
    (dgFourLastHornSourceRefinement_topResidual σ H.q H.s) hc
  have ha : differential A H.a = dgGradedPrecompose A D (-2) (dgFourLastHornTopResidual σ) H.s +
      compose A ((HornData.knownData σ).edgeHom 3 4 (by decide)) H.Q (by decide) :=
    H.a_differential
  exact eq_of_heq ((hd.trans (heq_of_eq ha)).trans hr.symm)

/-- 原始元の同じ実 Q・A は、細分した実ホーンの型付き二未知解を与える。 -/
def DGFourLastHornResidualRefinement.solution :
    DGFourLastHornSolution (dgFourLastHornSourceRefinement σ H.q H.s) :=
  ⟨H.refinedQ, H.refinedQ_differential, H.refinedA, H.refinedA_differential⟩

/-- 細分ホーンの充填は元の指定終端面を厳密に保つ。 -/
lemma dgFourLastHornSourceRefinement_filler_face0
    (F : Δ[4] ⟶ dgNerve A D)
    (hF : (horn 4 4).ι ≫ F = dgFourLastHornSourceRefinement σ H.q H.s) :
    SSet.stdSimplex.δ (0 : Fin 5) ≫ F = horn.ι (4 : Fin 5) 0 (by decide) ≫ σ := by
  rw [← horn.ι_ι_assoc (4 : Fin 5) 0 (by decide), hF,
    dgFourLastHornSourceRefinement_preserves_face0]

/-- 最後辺が実分母の実ホーンは、追加実閉分母後に全体を実際に充填できる。 -/
theorem dgFourLastHorn_exists_sourceRefinement_filler [IsDGPretriangulated A D]
    (P : Set D) (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)
    (hW : (dgClosedEdge A D (dgFourLastHornFinalClosed σ)).edge ∈ dgVerdierEdges A D P) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
        ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0)),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∃ F : Δ[4] ⟶ dgNerve A D,
          (horn 4 4).ι ≫ F = dgFourLastHornSourceRefinement σ q s := by
  obtain ⟨H⟩ := dgFourLastHornResidualRefinement_nonempty P σ hW
  exact ⟨H.q, H.s, H.denominator, H.solution.extension, H.solution.fac⟩

end SerrePositivity.InfinityCategories
