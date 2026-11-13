module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverRefinement

/-! # 厳密屋根の細分射と元の実 Verdier 分母

概要：厳密屋根添字の任意の射の閉始域成分は、元の実 Verdier 分母である。
方針：実 over 比較の始域射影の一致を一単体で評価し、実細分の分母判定へ渡す。
規約：比較の充満忠実性は仮定しない。使われ方：商側の屋根図式の細分写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 閉射の通常の nerve 辺の包含像は、元の指定実閉辺。 -/
lemma closedNerveInclusion_mk₁ {q x : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (s : q ⟶ x) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ s) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv A D).injective
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_edge]
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    rfl

/-- 厳密屋根の始域写像は、指定閉細分射の通常の nerve 辺を回収する。 -/
lemma dgClosedRoofNerveSourceMap_edge (P : Set D) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofNerveSourceMap A D P x).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ r) = ComposableArrows.mk₁ r.hom.left := by
  refine ComposableArrows.ext₁
    (F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofNerveSourceMap A D P x).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ r))
    (G := ComposableArrows.mk₁ r.hom.left) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 厳密屋根の細分辺の始域射影は、元の閉細分射の実辺そのもの。 -/
lemma dgClosedRoofVerdierMap_edge_source (P : Set D) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x).app (Opposite.op ⦋1⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ r)) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge := by
  have h := congrArg (fun F => F.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ r))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap_source A D P x)
  refine h.trans ?_
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A D).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofNerveSourceMap A D P x).app _ (ComposableArrows.mk₁ r)) = _
  rw [dgClosedRoofNerveSourceMap_edge, closedNerveInclusion_mk₁]

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 厳密屋根の任意の細分射の始域成分は元の実 Verdier 分母である。 -/
lemma dgClosedRoofRefinement_mem (P : Set D) (x : D)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (r : s ⟶ t) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r.hom.left).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource_edge_mem A D P x
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofVerdierMap A D P x).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ r))
  rw [dgClosedRoofVerdierMap_edge_source] at h
  exact h

/-- 既存の厳密屋根を指定実閉分母で細分した屋根。 -/
def dgClosedRoofRefine (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) {q : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ s.obj.left)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x :=
  ⟨Over.mk (r ≫ s.obj.hom), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P r s.obj.hom hr s.property⟩

/-- 指定実分母による細分は、元の厳密屋根添字への実際の射を持つ。 -/
def dgClosedRoofRefineHom (P : Set D) (x : D)
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x) {q : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ s.obj.left)
    (hr : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D r).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    dgClosedRoofRefine A D P x s r hr ⟶ s :=
  ObjectProperty.homMk (Over.homMk r rfl)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
