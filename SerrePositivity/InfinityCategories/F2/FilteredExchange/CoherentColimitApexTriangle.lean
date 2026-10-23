module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitCoconeTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueTriangleSquare

/-!
概要：元の余極限二単体へ、全 Hom 比較の指定 path の整合式を適用する。
方針：元の持ち上げの頂点評価を使い、三つの元の余極限辺を厳密に回収する。
規約：三辺も精密化辺も再選択しない。使われ方：単位三角柱と a6 の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の全関手二単体の、元の余極限関手による同じ全二単体の像。 -/
def coherentColimitApexTriangle : SpaceInfinity.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (T.diagram ≫ coherentColimitFunctor B)

/-- 最初の面は、元の最初の円柱に余極限関手を適用した指定辺そのもの。 -/
lemma coherentColimitApexTriangle_first :
    SpaceInfinity.δ 2 (coherentColimitApexTriangle B T) =
      (coherentColimitFunctorEdge B l).edge := by
  rw [coherentColimitApexTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, T.face_two, SSet.yonedaEquiv_comp]
  rfl

/-- 最後の面も、元の最後の円柱の同じ余極限辺。 -/
lemma coherentColimitApexTriangle_last :
    SpaceInfinity.δ 0 (coherentColimitApexTriangle B T) =
      (coherentColimitFunctorEdge B r).edge := by
  rw [coherentColimitApexTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, T.face_zero, SSet.yonedaEquiv_comp]
  rfl

/-- 長辺の面も、元の共有対角円柱の同じ余極限辺。 -/
lemma coherentColimitApexTriangle_long :
    SpaceInfinity.δ 1 (coherentColimitApexTriangle B T) =
      (coherentColimitFunctorEdge B d).edge := by
  rw [coherentColimitApexTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, T.face_one, SSet.yonedaEquiv_comp]
  rfl

/-- 元の余極限三角形の指定同型は、同じ精密化の輸送と指定両端比較で整合する。 -/
lemma coherentColimitApexTriangle_isoSquare :
    let s := coherentColimitApexTriangle B T
    ((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom ≪≫
      pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)) =
    pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s)) ≪≫
      pointedValueTriangleTransportIso s :=
  pointedValueTriangle_isoSquare (coherentColimitApexTriangle B T)

end SerrePositivity.InfinityCategories.F2
