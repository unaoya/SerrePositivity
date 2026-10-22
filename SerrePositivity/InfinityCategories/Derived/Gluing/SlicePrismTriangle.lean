module
public import SerrePositivity.InfinityCategories.Derived.Gluing.JoinParameterComparison
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! slice の全 prism を具体的な二単体族へ展開し、射影と両端を三辺に保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}

lemma dgGluingJoinEdgePoint_front_inv :
    stdSimplex.δ (2 : Fin 3) ≫ (joinStdSimplexIso.{u} 1 0).inv = joinInl Δ[1] Δ[0] := by
  apply (cancel_mono (joinStdSimplexIso 1 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, joinStdSimplexIso_one_inl]

lemma dgGluingJoinEdgePoint_face_inv (i : Fin 2) :
    stdSimplex.δ i.castSucc ≫ (joinStdSimplexIso.{u} 1 0).inv =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (stdSimplex.δ i) (𝟙 Δ[0]) := by
  apply (cancel_mono (joinStdSimplexIso 1 0).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    joinStdSimplexIso_one_vertex, Iso.inv_hom_id_assoc]

def dgGluingSlicePrismEdgeFamily (a : (Δ[0] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    (Δ[1] : SSet.{u}) ⊗ K ⟶ X :=
  ((joinStdSimplexIso 0 0).inv ▷ K) ≫
    dgGluingJoinParameterComparison Δ[0] Δ[0] K ≫ sliceOverUncurry a

def dgGluingSlicePrismTriangle (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    (Δ[2] : SSet.{u}) ⊗ K ⟶ X :=
  ((joinStdSimplexIso 1 0).inv ▷ K) ≫
    dgGluingJoinParameterComparison Δ[1] Δ[0] K ≫ sliceOverUncurry s

lemma dgGluingSlicePrismTriangle_front (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s =
      s ≫ sliceOverProjection p := by
  have hi := dgGluingJoinParameterComparison_inl (Δ[1] : SSet.{u}) Δ[0] K
  rw [dgGluingSlicePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    dgGluingJoinEdgePoint_front_inv, reassoc_of% hi, sliceOverUncurry_projection]

lemma dgGluingSlicePrismTriangle_face (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p)
    (i : Fin 2) :
    (stdSimplex.δ i.castSucc ▷ K) ≫ dgGluingSlicePrismTriangle s =
      dgGluingSlicePrismEdgeFamily ((stdSimplex.δ i ▷ K) ≫ s) := by
  have hn := dgGluingJoinParameterComparison_left (Δ[0] : SSet.{u}) Δ[0] K (stdSimplex.δ i)
  rw [dgGluingSlicePrismTriangle, ← Category.assoc, ← comp_whiskerRight,
    dgGluingJoinEdgePoint_face_inv, comp_whiskerRight, Category.assoc,
    reassoc_of% hn, ← sliceOverUncurry_precomp]
  rfl

end SerrePositivity.InfinityCategories
