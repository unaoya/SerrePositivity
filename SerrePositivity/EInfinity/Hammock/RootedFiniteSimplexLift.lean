module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteDiagram
public import SerrePositivity.EInfinity.Hammock.FiniteGridRootHull

/-!
# 元の固定語の各単体の有限包への持ち上げ

概要：元の全体の各 grid は同じ有限部分集合図式の一項の像となる。
方針：元の全射列の支持と既存の厳密な grid の回収式を使う。
規約：元の同じ語と単体次数を保持する。
使われ方：固定語の graph の余極限の全射性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q) (a : Word) (n : SimplexCategoryᵒᵖ)

def liftSimplex (σ : (graph (⊤ : MorphismProperty (Paths Q)) a
    ((Paths.of Q).obj X) ((Paths.of Q).obj Y)).obj n) :
    ((graphDiagram T X Y a).obj (gridPathSupport σ)).obj n := by
  letI := FiniteQuiver.quiver (hull T X Y (gridPathSupport σ))
  exact FiniteGrid.rootedFunctor T σ

lemma liftSimplex_projection (σ : (graph (⊤ : MorphismProperty (Paths Q)) a
    ((Paths.of Q).obj X) ((Paths.of Q).obj Y)).obj n) :
    ((graphCocone T X Y a).ι.app (gridPathSupport σ)).app n (liftSimplex T X Y a n σ) = σ := by
  let := FiniteQuiver.quiver (hull T X Y (gridPathSupport σ))
  exact FiniteGrid.rootedFunctor_projection T σ

lemma graphMap_projection {S R : Finset Q} (h : S ⊆ R) :
    (graphDiagram T X Y a).map (homOfLE h) ≫ nerveMap (projectionFunctor T X Y a R) =
      nerveMap (projectionFunctor T X Y a S) := by
  change nerveMap (mapFunctor T X Y a h) ≫ nerveMap (projectionFunctor T X Y a R) = _
  change nerveMap (mapFunctor T X Y a h ⋙ projectionFunctor T X Y a R) = _
  exact congrArg nerveMap (mapFunctor_projection T X Y a h)

end SerrePositivity.EInfinity.Hammock.RootedFinite
