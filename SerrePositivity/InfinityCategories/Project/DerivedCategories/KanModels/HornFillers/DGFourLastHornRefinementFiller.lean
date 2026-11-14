module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornRefinedResiduals
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornRefinedCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornRefinementFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornSolution

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

variable [Small.{u} D] {P : Set D}
variable {σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
variable (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornResidualRefinement P σ)

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 Q。 -/
def DGFourLastHornResidualRefinement.refinedQ :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s)).obj 3) (-2) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj3 σ H.q H.s).symm (-2) H.Q

/-- 新ホーンの回収対象族に沿って型を移した、同じ実 A。 -/
def DGFourLastHornResidualRefinement.refinedA :
    GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s)).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s)).obj 4) (-3) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj4 σ H.q H.s).symm (-3) H.a

/-- 型だけを移した Q は元の回収 Q と一致する。 -/
lemma DGFourLastHornResidualRefinement.refinedQ_heq : HEq H.refinedQ H.Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport_heq _ _ _ _

/-- 型だけを移した A は元の回収 A と一致する。 -/
lemma DGFourLastHornResidualRefinement.refinedA_heq : HEq H.refinedA H.a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedHomTransport_heq _ _ _ _

/-- 回収した Q は、貼った新ホーンの欠けた三次面の微分式を満たす。 -/
lemma DGFourLastHornResidualRefinement.refinedQ_differential :
    differential A H.refinedQ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj3 σ H.q H.s) rfl H.refinedQ H.Q H.refinedQ_heq
  have hq : _root_.SerrePositivity.DifferentialGraded.differential A H.Q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-2 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ) H.s :=
    H.Q_differential
  exact eq_of_heq ((hd.trans (heq_of_eq hq)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_missingResidual σ H.q H.s).symm)

/-- 回収した A は、貼った新ホーンの同じ Q と最上位微分式を満たす。 -/
lemma DGFourLastHornResidualRefinement.refinedA_differential :
    _root_.SerrePositivity.DifferentialGraded.differential A H.refinedA =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s) +
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s)).edgeHom
        3 4 (by decide)) H.refinedQ (by decide) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl H.refinedA H.a H.refinedA_heq
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (k := -2) (k' := -2)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj3 σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl rfl rfl _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_lastEdge σ H.q H.s) H.refinedQ_heq (by decide) (by decide)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_add_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj0 σ H.q H.s)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_obj4 σ H.q H.s) rfl _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_topResidual σ H.q H.s) hc
  have ha : differential A H.a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (-2) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ) H.s +
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide)) H.Q (by decide) :=
    H.a_differential
  exact eq_of_heq ((hd.trans (heq_of_eq ha)).trans hr.symm)

/-- 原始元の同じ実 Q・A は、細分した実ホーンの型付き二未知解を与える。 -/
def DGFourLastHornResidualRefinement.solution :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornSolution (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s) :=
  ⟨H.refinedQ, H.refinedQ_differential, H.refinedA, H.refinedA_differential⟩

/-- 細分ホーンの充填は元の指定終端面を厳密に保つ。 -/
lemma dgFourLastHornSourceRefinement_filler_face0
    (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ H.q H.s) :
    SSet.stdSimplex.δ (0 : Fin 5) ≫ F = horn.ι (4 : Fin 5) 0 (by decide) ≫ σ := by
  rw [← horn.ι_ι_assoc (4 : Fin 5) 0 (by decide), hF,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_preserves_face0]

/-- 最後辺が実分母の実ホーンは、追加実閉分母後に全体を実際に充填できる。 -/
theorem dgFourLastHorn_exists_sourceRefinement_filler [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hW : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFinalClosed σ)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
        ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∃ F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D,
          (horn 4 4).ι ≫ F = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement σ q s := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornResidualRefinement_nonempty P σ hW
  exact ⟨H.q, H.s, H.denominator, H.solution.extension, H.solution.fac⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
