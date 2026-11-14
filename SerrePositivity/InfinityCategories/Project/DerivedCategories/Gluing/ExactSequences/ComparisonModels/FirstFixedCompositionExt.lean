module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.FirstFixedCompositionDiagonal

/-! 始辺固定の合成対応への全パラメーターの射は、元の三角形だけで一意に決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)

lemma dgGluingFirstFixedCompositionSecond_uncurry
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSpace f z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) =
      (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ uncurry (a ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, uncurry_natural_left]
  change (Δ[1] ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z) =
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
      (Δ[2] ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation f z
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionEvaluation_last]

lemma dgGluingFirstFixedComposition_hom_ext_triangle
    (a b : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSpace f z)
    (h : a ≫ pullback.fst ((pre (horn 2 1).ι).app X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z) =
      b ≫ pullback.fst ((pre (horn 2 1).ι).app X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionHornMap f z)) : a = b := by
  apply pullback.hom_ext
  · exact h
  · change a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z =
      b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f z
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective y z
    rw [dgGluingFirstFixedCompositionSecond_uncurry,
      dgGluingFirstFixedCompositionSecond_uncurry, h]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
