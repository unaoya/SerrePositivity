module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.JoinParameterComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! slice の全 prism を具体的な二単体族へ展開し、射影と両端を三辺に保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}

lemma dgGluingJoinEdgePoint_front_inv :
    stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[0] := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl]

lemma dgGluingJoinEdgePoint_face_inv (i : Fin 2) :
    stdSimplex.δ i.castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0]) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Iso.inv_hom_id_assoc]

def dgGluingSlicePrismEdgeFamily (a : (Δ[0] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    (Δ[1] : SSet.{u}) ⊗ K ⟶ X :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ▷ K) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison Δ[0] Δ[0] K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a

def dgGluingSlicePrismTriangle (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    (Δ[2] : SSet.{u}) ⊗ K ⟶ X :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ▷ K) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison Δ[1] Δ[0] K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry s

lemma dgGluingSlicePrismTriangle_front (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s =
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison_inl (Δ[1] : SSet.{u}) Δ[0] K
  rw [dgGluingSlicePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    dgGluingJoinEdgePoint_front_inv, reassoc_of% hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection]

lemma dgGluingSlicePrismTriangle_face (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)
    (i : Fin 2) :
    (stdSimplex.δ i.castSucc ▷ K) ≫ dgGluingSlicePrismTriangle s =
      dgGluingSlicePrismEdgeFamily ((stdSimplex.δ i ▷ K) ≫ s) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterComparison_left (Δ[0] : SSet.{u}) Δ[0] K (stdSimplex.δ i)
  rw [dgGluingSlicePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    dgGluingJoinEdgePoint_face_inv, comp_whiskerRight, Category.assoc,
    reassoc_of% hn, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
