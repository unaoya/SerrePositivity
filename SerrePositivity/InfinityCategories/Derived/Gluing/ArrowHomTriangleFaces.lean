module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomTrianglePair

/-! 二つの実合成三角形の残る二辺は、元の Hom 族の両端成分評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {T X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⟶ X}
  (f : T ⟶ intervalMappingSpace (functorVertex F) (functorVertex G))

lemma dgGluingArrowHomTriangle_first_last :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
        (dgGluingArrowHomTrianglePairOfInterval F G f).first =
      intervalMappingUncurry (f ≫ intervalMappingPostOfEq
        (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (functorVertex F) (functorVertex G)
        (evaluateFunctorAt_functorVertex _ F) (evaluateFunctorAt_functorVertex _ G)) := by
  change (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
    ((squareTriangle 0 ▷ T) ≫ intervalFunctorHomPrism f) = _
  rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_upper_top]
  exact intervalFunctorHomPrism_evaluate f (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

lemma dgGluingArrowHomTriangle_second_first :
    (stdSimplex.δ (2 : Fin 3) ▷ T) ≫
        (dgGluingArrowHomTrianglePairOfInterval F G f).second =
      intervalMappingUncurry (f ≫ intervalMappingPostOfEq
        (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
        (functorVertex F) (functorVertex G)
        (evaluateFunctorAt_functorVertex _ F) (evaluateFunctorAt_functorVertex _ G)) := by
  change (stdSimplex.δ (2 : Fin 3) ▷ T) ≫
    ((squareTriangle 1 ▷ T) ≫ intervalFunctorHomPrism f) = _
  rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_lower_bottom]
  exact intervalFunctorHomPrism_evaluate f (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

end SerrePositivity.InfinityCategories
