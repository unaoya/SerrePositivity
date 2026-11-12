module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SlicePrismTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.JoinParameterIntervalPrism

/-! 具体的な slice 三角形の対角・終辺は、元の prism の両端の同じ区間評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}

lemma dgGluingIntervalFace_zero (K : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [whiskerRight_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_fst,
      stdSimplex.δ_zero_eq_const, SSet.comp_const]
  · simp only [whiskerRight_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_snd, Category.comp_id]

lemma dgGluingIntervalFace_one (K : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 2) ▷ K) = snd (Δ[0] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [whiskerRight_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_fst,
      stdSimplex.δ_one_eq_const, SSet.comp_const]
  · simp only [whiskerRight_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.assoc, lift_snd, Category.comp_id]

lemma dgGluingSlicePrismEdgeFamily_constant (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismEdgeFamily (snd (Δ[0] : SSet.{u}) K ≫ a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismEdgeFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]
  have hh := congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingJoinParameterIntervalPrism K)
  simpa only [Category.assoc] using hh

lemma dgGluingSlicePrismTriangle_zero (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ s) := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_face s (0 : Fin 2)
  change (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle s = _ at hh
  refine hh.trans ?_
  rw [dgGluingIntervalFace_zero, Category.assoc, dgGluingSlicePrismEdgeFamily_constant]

lemma dgGluingSlicePrismTriangle_one (s : (Δ[1] : SSet.{u}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ s) := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle_face s (1 : Fin 2)
  change (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle s = _ at hh
  refine hh.trans ?_
  rw [dgGluingIntervalFace_one, Category.assoc, dgGluingSlicePrismEdgeFamily_constant]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
