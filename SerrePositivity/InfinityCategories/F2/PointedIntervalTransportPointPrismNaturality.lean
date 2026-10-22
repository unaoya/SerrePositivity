module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTransportPointPrism

/-!
概要：元の指定点の普遍輸送 prism の実始域への制限は、同じ初期値の前合成になる。
方針：同じ指定点を持つ直積射の厳密な自然性を使う。
規約：普遍 prism と指定点を保持。使われ方：全第一辺の三角形族を元の実頂点へ制限する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定点の普遍 prism の制限は、同じ始点射を前合成した普遍 prism そのもの。 -/
lemma pointedIntervalTransportPointPrism_precomp {K C T : SSet.{u + 1}}
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (l : T _⦋0⦌)
    (f : K ⟶ vertexFiber pointedSpaceProjection x) (r : C ⟶ K) :
    (Δ[1] ◁ r) ≫ pointedIntervalTransportPointPrism a l f =
      pointedIntervalTransportPointPrism a l (r ≫ f) := by
  unfold pointedIntervalTransportPointPrism
  rw [← Category.assoc, ← whiskerLeft_comp]
  have hn : r ≫ lift f (SSet.const l) = lift (r ≫ f) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [hn]

/-- 元の指定余極限辺の普遍 prism も、同じ全初期値の実前合成と厳密に可換する。 -/
lemma coherentColimitRawTransportPointPrism_precomp (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : SSet.Homotopy F G) {K C : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (r : C ⟶ K) :
    (Δ[1] ◁ r) ≫ coherentColimitRawTransportPointPrism B a f =
      coherentColimitRawTransportPointPrism B a (r ≫ f) :=
  pointedIntervalTransportPointPrism_precomp _ _ f r

end SerrePositivity.InfinityCategories.F2
