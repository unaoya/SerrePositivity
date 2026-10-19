module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinedResiduals
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinedCochains

/-! # 追加実閉分母後の指定最後外ホーンの実充填

概要：既供給の原始元から回収した Q・A を新対象族へ移し、細分した実ホーン全体を充填する。
方針：新旧対象の等式と cochain の異種等号で二微分式を輸送し、既存の実充填へ渡す。
規約：元の終端面を厳密に保つ。使われ方：実分母図式の辺上の整合性の供給。
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

/-- 始域・終域の指定等式で、元の斉次 Hom 元を輸送する。 -/
def dgGradedHomTransport {x y x' y' : D} (hx : x = x') (hy : y = y') (n : ℤ)
    (f : GradedHom A x y n) : GradedHom A x' y' n := cast (by rw [hx, hy]) f

/-- 指定対象等式による輸送は、元の cochain と異種等号で一致する。 -/
lemma dgGradedHomTransport_heq {x y x' y' : D} (hx : x = x') (hy : y = y') (n : ℤ)
    (f : GradedHom A x y n) : HEq (dgGradedHomTransport hx hy n f) f := by
  cases hx
  cases hy
  rfl

variable [Small.{u} D] {P : Set D}
variable {σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D}
variable (H : DGLastHornResidualRefinement P σ)

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 Q。 -/
def DGLastHornResidualRefinement.refinedQ :
    GradedHom A ((HornData.knownData (dgLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgLastHornSourceRefinement σ H.q H.s)).obj 2) (-1) :=
  dgGradedHomTransport (dgLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (dgLastHornSourceRefinement_obj2 σ H.q H.s).symm (-1) H.Q

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 A。 -/
def DGLastHornResidualRefinement.refinedA :
    GradedHom A ((HornData.knownData (dgLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((HornData.knownData (dgLastHornSourceRefinement σ H.q H.s)).obj 3) (-2) :=
  dgGradedHomTransport (dgLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (dgLastHornSourceRefinement_obj3 σ H.q H.s).symm (-2) H.a

/-- 型だけを移した Q は元の回収 Q と一致する。 -/
lemma DGLastHornResidualRefinement.refinedQ_heq : HEq H.refinedQ H.Q :=
  dgGradedHomTransport_heq _ _ _ _

/-- 型だけを移した A は元の回収 A と一致する。 -/
lemma DGLastHornResidualRefinement.refinedA_heq : HEq H.refinedA H.a :=
  dgGradedHomTransport_heq _ _ _ _

/-- 回収した Q は、貼った新ホーンの欠けた三角形の微分式を満たす。 -/
lemma DGLastHornResidualRefinement.refinedQ_differential :
    differential A H.refinedQ = dgLastHornMissingResidual
      (dgLastHornSourceRefinement σ H.q H.s) := by
  have hd := gradedHom_differential_heq (dgLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgLastHornSourceRefinement_obj2 σ H.q H.s) rfl H.refinedQ H.Q H.refinedQ_heq
  have hq : differential A H.Q = dgGradedPrecompose A D 0 (dgLastHornMissingResidual σ) H.s :=
    H.Q_differential
  exact eq_of_heq ((hd.trans (heq_of_eq hq)).trans
    (dgLastHornSourceRefinement_missingResidual σ H.q H.s).symm)

/-- 回収した A は、貼った新ホーンの同じ Q と最上位微分式を満たす。 -/
lemma DGLastHornResidualRefinement.refinedA_differential :
    differential A H.refinedA = dgLastHornTopResidual (dgLastHornSourceRefinement σ H.q H.s) +
      compose A ((HornData.knownData (dgLastHornSourceRefinement σ H.q H.s)).edgeHom
        2 3 (by decide)) H.refinedQ (by decide) := by
  have hd := gradedHom_differential_heq (dgLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgLastHornSourceRefinement_obj3 σ H.q H.s) rfl H.refinedA H.a H.refinedA_heq
  have hc := gradedHom_compose_heq (k := -1) (k' := -1)
    (dgLastHornSourceRefinement_obj0 σ H.q H.s) (dgLastHornSourceRefinement_obj2 σ H.q H.s)
    (dgLastHornSourceRefinement_obj3 σ H.q H.s) rfl rfl rfl _ _ _ _
    (dgLastHornSourceRefinement_edge23 σ H.q H.s) H.refinedQ_heq (by decide) (by decide)
  have hr := gradedHom_add_heq (dgLastHornSourceRefinement_obj0 σ H.q H.s)
    (dgLastHornSourceRefinement_obj3 σ H.q H.s) rfl _ _ _ _
    (dgLastHornSourceRefinement_topResidual σ H.q H.s) hc
  have ha : differential A H.a = dgGradedPrecompose A D (-1) (dgLastHornTopResidual σ) H.s +
      compose A ((HornData.knownData σ).edgeHom 2 3 (by decide)) H.Q (by decide) :=
    H.a_differential
  exact eq_of_heq ((hd.trans (heq_of_eq ha)).trans hr.symm)

/-- 原始元の同じ実 Q・A は、細分した実ホーンの型付き二未知解を与える。 -/
def DGLastHornResidualRefinement.solution :
    DGLastHornSolution (dgLastHornSourceRefinement σ H.q H.s) :=
  ⟨H.refinedQ, H.refinedQ_differential, H.refinedA, H.refinedA_differential⟩

/-- 細分ホーンの充填は元の指定終端面を厳密に保つ。 -/
lemma dgLastHornSourceRefinement_filler_face0
    (F : Δ[3] ⟶ dgNerve A D)
    (hF : (horn 3 3).ι ≫ F = dgLastHornSourceRefinement σ H.q H.s) :
    SSet.stdSimplex.δ (0 : Fin 4) ≫ F = horn.ι (3 : Fin 4) 0 (by decide) ≫ σ := by
  rw [← horn.ι_ι_assoc (3 : Fin 4) 0 (by decide), hF,
    dgLastHornSourceRefinement_preserves_face0]

/-- 最後辺が実分母の実ホーンは、追加実閉分母後に全体を実際に充填できる。 -/
theorem dgLastHorn_exists_sourceRefinement_filler [IsDGPretriangulated A D]
    (P : Set D) (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)
    (hW : (dgClosedEdge A D (dgLastHornFinalClosed σ)).edge ∈ dgVerdierEdges A D P) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
        ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0)),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∃ F : Δ[3] ⟶ dgNerve A D,
          (horn 3 3).ι ≫ F = dgLastHornSourceRefinement σ q s := by
  obtain ⟨H⟩ := dgLastHornResidualRefinement_nonempty P σ hW
  exact ⟨H.q, H.s, H.denominator, H.solution.extension, H.solution.fac⟩

end SerrePositivity.InfinityCategories
