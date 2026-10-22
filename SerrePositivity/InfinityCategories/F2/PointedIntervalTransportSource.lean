module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportPointPrism

/-!
概要：元の普遍輸送を同じ始点射で前合成した、元の比較の標的証拠を公開する。
方針：元の比較と同じ source 前合成を使い、実 prism と一点制限を回収する。
規約：普遍輸送は再選択しない。使われ方：指定比較と最後辺の実 prism の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K T : SSet.{u + 1}} {x y : SpaceInfinity.{u} _⦋0⦌}
  (f : K ⟶ vertexFiber pointedSpaceProjection x) (a : T ⟶ intervalMappingSpace x y)

/-- 元の指定輸送比較で用いる、同じ始点前合成後の普遍輸送証拠。 -/
def pointedIntervalTransportSource :
    FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a) := by
  simpa only [Category.comp_id] using (pointedIntervalTransport a).precomposeSource f

/-- 元の指定比較は、公開した同じ標的証拠への元の endpointIso そのもの。 -/
lemma pointedIntervalTransportComparison_eq_source
    (w : FiberTransportFamily (b := y) pointedSpaceProjection f (intervalMappingUncurry a)) :
    pointedIntervalTransportComparison f a w =
      w.endpointIso pointedSpaceProjection f (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) (pointedIntervalTransportSource f a) := rfl

/-- 同じ始点前合成後の実 prism は、元の普遍 prism の同じ前合成。 -/
lemma pointedIntervalTransportSource_prism :
    (pointedIntervalTransportSource f a).prism =
      (Δ[1] ◁ (f ▷ T)) ≫ (pointedIntervalTransport a).prism := rfl

/-- 同じ指定点で制限した実 prism は、同じ始点射と指定点の普遍輸送 prism。 -/
lemma pointedIntervalTransportSource_point_prism {C : SSet.{u + 1}} (s : C ⟶ K)
    (l : T _⦋0⦌) :
    (Δ[1] ◁ lift s (SSet.const l)) ≫ (pointedIntervalTransportSource f a).prism =
      pointedIntervalTransportPointPrism a l (s ≫ f) := by
  rw [pointedIntervalTransportSource_prism, ← Category.assoc, ← whiskerLeft_comp]
  have hn : lift s (SSet.const l) ≫ (f ▷ T) = lift (s ≫ f) (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  rw [hn]
  rfl

end SerrePositivity.InfinityCategories.F2
