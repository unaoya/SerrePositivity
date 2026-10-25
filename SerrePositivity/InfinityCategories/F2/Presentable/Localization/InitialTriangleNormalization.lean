module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonInitialTriangle
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactPresentationComparison
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes

/-!
概要：初期実三角形の二つの全脚を、小さい端点形状の持ち上げで正規化する。
方針：元の脚の一単体と標準単体の宇宙同型の自然性を使う。
規約：全余錐値の等式を保つ。使われ方：二表示の初期前置比較状態。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 元の点への全余錐制限は、同じ余錐脚が与える全 coslice 点である。 -/
lemma pointRestriction_coconeTransportLeg_val {B X : SSet.{u}} {D : B ⟶ X}
    (c : JoinCocone D) (b : B _⦋0⦌) :
    (c.restrict (SSet.yonedaEquiv.symm b)).val =
      (edgeCosliceVertex (coconeTransportLeg c b).toTruncated).val := by
  change joinMap (SSet.yonedaEquiv.symm b) (𝟙 Δ[0]) ≫ c.val =
    (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (coconeTransportLeg c b).edge
  rw [coconeTransportLeg_edge]
  change _ = (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm b) (𝟙 Δ[0]) ≫ c.val))
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- 持ち上げた元の点への制限も、同じ元の脚を全余錐値として保持する。 -/
lemma uliftPointRestriction_coconeTransportLeg_val {B : SSet.{u}} {X : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X}
    (c : JoinCocone D) (b : B _⦋0⦌) :
    (c.restrict ((SSet.uliftFunctor.{u + 1, u}).map (SSet.yonedaEquiv.symm b))).val =
      joinMap (uliftStdSimplexIso.{u, u + 1} 0).hom (𝟙 Δ[0]) ≫
        (edgeCosliceVertex (coconeTransportLeg c (ULift.up b)).toTruncated).val := by
  have hp : (SSet.uliftFunctor.{u + 1, u}).map (SSet.yonedaEquiv.symm b) =
      (uliftStdSimplexIso.{u, u + 1} 0).hom ≫ SSet.yonedaEquiv.symm (ULift.up b) := by
    rw [← uliftYonedaMap, Iso.hom_inv_id_assoc]
  change joinMap _ _ ≫ c.val = _
  rw [hp]
  change joinMap ((uliftStdSimplexIso.{u, u + 1} 0).hom ≫
    SSet.yonedaEquiv.symm (ULift.up b)) (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ c.val = _
  rw [joinMap_comp, Category.assoc]
  rw [← pointRestriction_coconeTransportLeg_val]
  rfl

/-- 標準辺の全余錐の持ち上げ正規化は、二つの端点の全制限と可換。 -/
lemma normalizedEdgeCocone_restrict_val {X : SSet.{u + 1}} {x y z : X _⦋0⦌}
    {e : X.Edge x y} {r : X.Edge y z} {f : X.Edge x z}
    (T : e.CompStruct r f) (i : Fin 2) :
    (((compStructCocone T).restrict (uliftStdSimplexIso.{u, u + 1} 1).hom).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (SSet.stdSimplex.δ i))).val =
    joinMap (uliftStdSimplexIso.{u, u + 1} 0).hom (𝟙 Δ[0]) ≫
      ((compStructCocone T).restrict (SSet.stdSimplex.δ i)).val := by
  change joinMap _ _ ≫ (joinMap _ _ ≫ (compStructCocone T).val) = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp]
  change joinMap ((uliftStdSimplexIso.{u, u + 1} 0).hom ≫
    (SSet.stdSimplex.δ i)) (𝟙 Δ[0] ≫ 𝟙 Δ[0]) ≫ (compStructCocone T).val = _
  rw [joinMap_comp, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
