module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawTriangleBase

/-!
概要：元の余極限関手の全二単体の三辺を、元の同じ指定辺の実一次単体へ戻す。
方針：同じ元の二単体の面式と全係数の第一射影を合成する。
規約：元の二単体・指定辺・全係数を保持。使われ方：raw 普遍二辺の全持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全二単体の指定面を任意の全係数で引き戻しても、元の指定余極限辺になる。 -/
lemma coherentColimitRawTriangle_face (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : SSet.Homotopy F G) {K : SSet.{u + 1}}
    (P : (Δ[2] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj
      SpaceInfinity.{u}) (i : Fin 3) (h : stdSimplex.δ i ≫ P = curry a.h) :
    (stdSimplex.δ i ▷ K) ≫ fst (Δ[2] : SSet.{u + 1}) K ≫ P ≫ coherentColimitFunctor B =
      fst (Δ[1] : SSet.{u + 1}) K ≫
        SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
  rw [coherentColimitFunctorEdge_simplex]
  rw [← Category.assoc (stdSimplex.δ i ▷ K), whiskerRight_fst]
  rw [Category.assoc, ← Category.assoc (stdSimplex.δ i), h]

end SerrePositivity.InfinityCategories.F2
