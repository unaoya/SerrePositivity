module

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SquareFamilyReading
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Stable.ReindexSliceOver
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns
public import SerrePositivity.InfinityCategories.Stable.UniverseSquareShape
public import SerrePositivity.InfinityCategories.Stable.UniverseUniversalSquares

/-!
概要：小さい cospan 全錐の宇宙持ち上げを、その同じ元の実四角形へ読み戻す。
方針：普遍四角形の既存の宇宙整合性を、正方形同型の逆向きへ移す。
規約：極限性を仮定しない、全写像の厳密な等式。
使われ方：Ind Yoneda の全錐族の各段を、元の C の実四角形に照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全錐を持ち上げて四角形へ読むことは、元の四角形を持ち上げることと一致する。 -/
lemma uliftConeSquareReading {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X}
    (c : JoinCone p) :
    (uliftCospanSquareReadingIso.{u, v}).inv ≫ (JoinCone.ulift.{u, v} c).val =
      uliftSquare.{u, v} (coneSquare c) := by
  have h := pullbackCone_ulift_reindex_val.{u, v} (coneSquare c)
  have hv : (pullbackCone (coneSquare c)).val = c.val := by
    change cospanConeSquareIso.hom ≫ (cospanConeSquareIso.inv ≫ c.val) = c.val
    rw [Iso.hom_inv_id_assoc]
  change joinMap (𝟙 Δ[0]) (uliftHornIso.{u, v} 2 2).inv ≫
    ((uliftConeShapeIso.{u, v} (horn 2 2 : SSet.{u}) 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (pullbackCone (coneSquare c)).val) =
    cospanConeSquareIso.hom ≫ uliftSquare (coneSquare c) at h
  rw [hv] at h
  change joinMap (𝟙 Δ[0]) (uliftHornIso.{u, v} 2 2).inv ≫
    (JoinCone.ulift.{u, v} c).val =
      cospanConeSquareIso.hom ≫ uliftSquare (coneSquare c) at h
  apply (cancel_epi cospanConeSquareIso.hom).mp
  simpa only [uliftCospanSquareReadingIso, Iso.trans_inv, joinIso, Iso.refl_inv,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h

end SerrePositivity.InfinityCategories.F2
