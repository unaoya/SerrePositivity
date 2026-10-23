module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleSequentialPostComparison

/-!
概要：標的図式の等式に沿って、元の全三角形の指定比較を輸送する。
方針：頂点等式を消去し、同じ実円柱と全二単体の外延性を使う。
規約：指定値を選び直さない。使われ方：単位二面の native 頂点への正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ二面の指定比較は、標的頂点の等式による型変更後も同じ値を持つ。 -/
lemma functorTriangleSequentialPostComparison_heq_target
    {B C : SSet.{u + 1}} {F G J J' : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    {b' : SSet.Homotopy G J'} {c' : SSet.Homotopy F J'}
    (T : FunctorCompositionTriangle a b c) (T' : FunctorCompositionTriangle a b' c')
    (hj : J = J') (hb : b.h = b'.h) (hc : c.h = c'.h)
    (ht : T.diagram = T'.diagram) (p : C ⟶ B) :
    HEq (functorTriangleSequentialPostComparison T p)
      (functorTriangleSequentialPostComparison T' p) := by
  subst J'
  have eb : b = b' := SSet.RelativeMorphism.Homotopy.ext hb
  have ec : c = c' := SSet.RelativeMorphism.Homotopy.ext hc
  subst b' c'
  have et : T = T' := by cases T; cases T'; cases ht; rfl
  subst T'
  rfl

/-- 標的の等式輸送は、全相対始域上の同じ各点の指定成分も保持する。 -/
lemma functorTriangleSequentialPostComparison_app_heq_target
    {B C : SSet.{u + 1}} {F G J J' : B ⟶ SpaceInfinity.{u}}
    {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
    {b' : SSet.Homotopy G J'} {c' : SSet.Homotopy F J'}
    (T : FunctorCompositionTriangle a b c) (T' : FunctorCompositionTriangle a b' c')
    (hj : J = J') (hb : b.h = b'.h) (hc : c.h = c'.h)
    (ht : T.diagram = T'.diagram) (p : C ⟶ B)
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq ((functorTriangleSequentialPostComparison T p).app x)
      ((functorTriangleSequentialPostComparison T' p).app x) := by
  subst J'
  have eb : b = b' := SSet.RelativeMorphism.Homotopy.ext hb
  have ec : c = c' := SSet.RelativeMorphism.Homotopy.ext hc
  subst b' c'
  have et : T = T' := by cases T; cases T'; cases ht; rfl
  subst T'
  rfl

end SerrePositivity.InfinityCategories.F2
