module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawConstantInterval
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTransportPointPrism

/-!
概要：元の指定 raw 辺の同じ実普遍輸送を、任意の係数空間へ定値な全輸送として保持する。
方針：元の実 prism と実終点を第一射影で引き戻す。
規約：輸送は再選択しない。使われ方：全第一辺選択の長辺に対する同じ固定比較先。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (d : SSet.Homotopy F J) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
  (L : SSet.{u + 1})
local notation "D" => SSet.const (coherentColimitRawIntervalVertex B d)

/-- 元の同じ raw 長辺普遍輸送を、全係数に定値な同じ全輸送として保持する。 -/
def coherentColimitRawConstantEdgeTransport :
    FiberTransportFamily (b := JoinCocone.vertex (coherentDiagramTotalCocone J))
      pointedSpaceProjection f (intervalMappingUncurry (D : L ⟶ _)) where
  endpoint := fst K L ≫ (f ≫ coherentColimitRawFiberTransport B d)
  prism := (Δ[1] ◁ fst K L) ≫ coherentColimitRawTransportPointPrism B d f
  start := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coherentColimitRawTransportPointPrism_start]
  finish := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coherentColimitRawTransportPointPrism_finish]
    simp only [Category.assoc]
  over_base := by
    rw [Category.assoc, coherentColimitRawTransportPointPrism_projection,
      coherentColimitRawConstantInterval_uncurry, ← Category.assoc, whiskerLeft_fst,
      ← Category.assoc, whiskerLeft_fst]

/-- 同じ全定値輸送の Hom 作用は、同じ実普遍輸送の合成射の定値族そのもの。 -/
lemma coherentColimitRawConstantEdgeTransport_map :
    (coherentColimitRawConstantEdgeTransport B d f L).map =
      SSet.const (functorVertex (f ≫ coherentColimitRawFiberTransport B d)) := by
  apply uncurry_injective
  rw [FiberTransportFamily.map, uncurry_curry, uncurry_const_functorVertex]
  rfl

end SerrePositivity.InfinityCategories.F2
