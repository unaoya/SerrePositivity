module
public import SerrePositivity.InfinityCategories.Derived.Gluing.SlicePrismTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.JoinParameterIntervalPrism

/-! 具体的な slice 三角形の対角・終辺は、元の prism の両端の同じ区間評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}

lemma dgGluingIntervalFace_zero (K : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ prismEndpoint 1 K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [whiskerRight_fst, prismEndpoint, Category.assoc, lift_fst,
      stdSimplex.δ_zero_eq_const, SSet.comp_const]
  · simp only [whiskerRight_snd, prismEndpoint, Category.assoc, lift_snd, Category.comp_id]

lemma dgGluingIntervalFace_one (K : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ prismEndpoint 0 K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [whiskerRight_fst, prismEndpoint, Category.assoc, lift_fst,
      stdSimplex.δ_one_eq_const, SSet.comp_const]
  · simp only [whiskerRight_snd, prismEndpoint, Category.assoc, lift_snd, Category.comp_id]

lemma dgGluingSlicePrismEdgeFamily_constant (a : K ⟶ sliceOver p) :
    dgGluingSlicePrismEdgeFamily (snd (Δ[0] : SSet.{u}) K ≫ a) =
      rightMappingSpacePrism K ≫ sliceOverUncurry a := by
  rw [dgGluingSlicePrismEdgeFamily, sliceOverUncurry_precomp]
  have hh := congrArg (fun k => k ≫ sliceOverUncurry a) (dgGluingJoinParameterIntervalPrism K)
  simpa only [Category.assoc] using hh

lemma dgGluingSlicePrismTriangle_zero (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s =
      rightMappingSpacePrism K ≫ sliceOverUncurry (prismEndpoint 1 K ≫ s) := by
  have hh := dgGluingSlicePrismTriangle_face s (0 : Fin 2)
  change (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s = _ at hh
  refine hh.trans ?_
  rw [dgGluingIntervalFace_zero, Category.assoc, dgGluingSlicePrismEdgeFamily_constant]

lemma dgGluingSlicePrismTriangle_one (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceOver p) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s =
      rightMappingSpacePrism K ≫ sliceOverUncurry (prismEndpoint 0 K ≫ s) := by
  have hh := dgGluingSlicePrismTriangle_face s (1 : Fin 2)
  change (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingSlicePrismTriangle s = _ at hh
  refine hh.trans ?_
  rw [dgGluingIntervalFace_one, Category.assoc, dgGluingSlicePrismEdgeFamily_constant]

end SerrePositivity.InfinityCategories
