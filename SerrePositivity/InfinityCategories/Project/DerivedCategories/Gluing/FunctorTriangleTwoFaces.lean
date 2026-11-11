module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitSpanTriangles
/-! # 指定した二面を保つ三角形の第三辺

概要：実二単体の二面を合成可能な二変形として指定し、第三辺を同じ二単体から取り出す。
方針：残る辺を関手辺から実ホモトピーへ戻す。
規約：二単体や指定二辺を選び直さず、第三辺も同じ二単体の面とする。
使われ方：augmentation 四面体からの実補正対角三角形を合成三角形として公開する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K E : SSet.{u}} {f g h : K ⟶ E}
def dgGluingFunctorTriangleThirdEdge (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
    (T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj E)
    (hl : stdSimplex.δ (2 : Fin 3) ≫ T = curry l.h)
    (hr : stdSimplex.δ (0 : Fin 3) ≫ T = curry r.h) : SSet.Truncated.Edge
    (X := (truncation 2).obj ((ihom K).obj E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h) where
  edge := SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T)
  src_eq := by
    change ((ihom K).obj E).δ 1 (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T)) = _
    have he : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
        stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      apply SSet.stdSimplex.ext
      intro j
      fin_cases j
      rfl
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, he, Category.assoc, hl]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l).src_eq
  tgt_eq := by
    change ((ihom K).obj E).δ 0 (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T)) = _
    have he : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
      apply SSet.yonedaEquiv.injective
      apply SSet.stdSimplex.ext
      intro j
      fin_cases j
      rfl
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, he, Category.assoc, hr]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r).tgt_eq

def dgGluingFunctorTriangleThirdHomotopy (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
    (T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj E)
    (hl : stdSimplex.δ (2 : Fin 3) ≫ T = curry l.h)
    (hr : stdSimplex.δ (0 : Fin 3) ≫ T = curry r.h) : SSet.Homotopy f h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (dgGluingFunctorTriangleThirdEdge l r T hl hr)
def dgGluingFunctorTriangleOfTwoFaces (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
    (T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj E)
    (hl : stdSimplex.δ (2 : Fin 3) ≫ T = curry l.h)
    (hr : stdSimplex.δ (0 : Fin 3) ≫ T = curry r.h) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (dgGluingFunctorTriangleThirdHomotopy l r T hl hr) where
  diagram := T
  face_zero := hr
  face_two := hl
  face_one := by
    change stdSimplex.δ (1 : Fin 3) ≫ T =
      curry (uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T))))
    rw [Equiv.symm_apply_apply, curry_uncurry]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
