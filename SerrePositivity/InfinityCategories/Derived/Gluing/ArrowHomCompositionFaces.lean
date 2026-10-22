module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowEdgeEvaluation

/-! 二合成三角形の可変辺を、元の四頂点を端点とする同じ Hom 族へ正規化する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)
  (h : T ⟶ intervalMappingSpace (functorVertex (SSet.yonedaEquiv.symm f.edge))
    (functorVertex (SSet.yonedaEquiv.symm g.edge)))

def dgGluingArrowHomSourceComponent : T ⟶ intervalMappingSpace a c :=
  h ≫ intervalMappingPostOfEq (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    _ _ (dgGluingArrowEdgeEvaluation_zero f) (dgGluingArrowEdgeEvaluation_zero g)

def dgGluingArrowHomTargetComponent : T ⟶ intervalMappingSpace b d :=
  h ≫ intervalMappingPostOfEq (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    _ _ (dgGluingArrowEdgeEvaluation_one f) (dgGluingArrowEdgeEvaluation_one g)

lemma dgGluingArrowHomFirstTriangle_last :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
      (dgGluingArrowHomTrianglePairOfInterval _ _ h).first =
      intervalMappingUncurry (dgGluingArrowHomTargetComponent f g h) := by
  change (stdSimplex.δ (0 : Fin 3) ▷ T) ≫
    ((squareTriangle 0 ▷ T) ≫ intervalFunctorHomPrism h) = _
  rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_upper_top]
  exact intervalFunctorHomPrism_evaluateOfEq h _
    (dgGluingArrowEdgeEvaluation_one f) (dgGluingArrowEdgeEvaluation_one g)

lemma dgGluingArrowHomSecondTriangle_first :
    (stdSimplex.δ (2 : Fin 3) ▷ T) ≫
      (dgGluingArrowHomTrianglePairOfInterval _ _ h).second =
      intervalMappingUncurry (dgGluingArrowHomSourceComponent f g h) := by
  change (stdSimplex.δ (2 : Fin 3) ▷ T) ≫
    ((squareTriangle 1 ▷ T) ≫ intervalFunctorHomPrism h) = _
  rw [← Category.assoc, ← comp_whiskerRight, triangleSquare_lower_bottom]
  exact intervalFunctorHomPrism_evaluateOfEq h _
    (dgGluingArrowEdgeEvaluation_zero f) (dgGluingArrowEdgeEvaluation_zero g)

end SerrePositivity.InfinityCategories
