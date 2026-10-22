module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionDiagonal

/-! 始辺固定の合成対応への全パラメーターの射は、元の三角形だけで一意に決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)

lemma dgGluingFirstFixedCompositionSecond_uncurry
    (a : T ⟶ dgGluingFirstFixedCompositionSpace f z) :
    intervalMappingUncurry (a ≫ dgGluingFirstFixedCompositionSecond f z) =
      (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ uncurry (a ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (dgGluingFirstFixedCompositionHornMap f z)) := by
  rw [intervalMappingUncurry_precomp, uncurry_natural_left]
  change (Δ[1] ◁ a) ≫ intervalMappingUncurry (dgGluingFirstFixedCompositionSecond f z) =
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
      (Δ[2] ◁ a) ≫ dgGluingFirstFixedCompositionEvaluation f z
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    dgGluingFirstFixedCompositionEvaluation_last]

lemma dgGluingFirstFixedComposition_hom_ext_triangle
    (a b : T ⟶ dgGluingFirstFixedCompositionSpace f z)
    (h : a ≫ pullback.fst ((pre (horn 2 1).ι).app X)
        (dgGluingFirstFixedCompositionHornMap f z) =
      b ≫ pullback.fst ((pre (horn 2 1).ι).app X)
        (dgGluingFirstFixedCompositionHornMap f z)) : a = b := by
  apply pullback.hom_ext
  · exact h
  · change a ≫ dgGluingFirstFixedCompositionSecond f z =
      b ≫ dgGluingFirstFixedCompositionSecond f z
    apply intervalMappingUncurry_injective y z
    rw [dgGluingFirstFixedCompositionSecond_uncurry,
      dgGluingFirstFixedCompositionSecond_uncurry, h]

end SerrePositivity.InfinityCategories
