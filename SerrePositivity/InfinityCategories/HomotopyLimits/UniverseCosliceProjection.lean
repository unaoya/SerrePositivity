module

public import SerrePositivity.InfinityCategories.Stable.UniverseSlices
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRestrictionIso

/-!
概要：元の coslice の宇宙比較と固定図式の制限は、元の射影と厳密に可換。
方針：可変標準単体の右包含と実錐写像の宇宙比較を全次数で照合する。
規約：元の図式と全単体を保持し、点での対応だけで代用しない。
使われ方：持ち上げた元の右 Kan 添字の pullback の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 錐の宇宙比較は、元の可変単体の右包含も標準単体の同型を介して保つ。 -/
lemma universeCoconeShapeIso_inr (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinInr K (Δ[n] : SSet.{u})) ≫
      (uliftCoconeShapeIso K n).hom =
    (uliftStdSimplexIso n).hom ≫
      joinInr ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, joinIso, ← Category.assoc, uliftJoinIso_inr, joinInr_joinMap]

/-- 逆向きの元の錐形状比較も可変単体の右包含を保つ。 -/
lemma universeCoconeShapeIso_inv_inr (K : SSet.{u}) (n : ℕ) :
    joinInr ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) ≫
      (uliftCoconeShapeIso K n).inv =
    (uliftStdSimplexIso n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinInr K (Δ[n] : SSet.{u})) := by
  apply (cancel_mono (uliftCoconeShapeIso K n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    universeCoconeShapeIso_inr, Iso.inv_hom_id_assoc]

/-- 元の全 coslice の宇宙比較は、元の標的への射影を厳密に保つ。 -/
lemma uliftSliceUnderIso_projection {K X : SSet.{u}} (p : K ⟶ X) :
    (uliftSliceUnderIso.{u, v} p).hom ≫
      sliceUnderProjection ((SSet.uliftFunctor.{v, u}).map p) =
    (SSet.uliftFunctor.{v, u}).map (sliceUnderProjection p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  change SSet.yonedaEquiv (joinInr _ _ ≫
      ((uliftCoconeShapeIso K n).inv ≫ (SSet.uliftFunctor.{v, u}).map s.val)) =
    ULift.up (SSet.yonedaEquiv (joinInr K (Δ[n] : SSet.{u}) ≫ s.val))
  rw [← Category.assoc, universeCoconeShapeIso_inv_inr, Category.assoc,
    ← Functor.map_comp]
  have h := uliftYonedaMap.{u, v} (SSet.yonedaEquiv (joinInr K (Δ[n] : SSet.{u}) ≫ s.val))
  rw [Equiv.symm_apply_apply] at h
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 元の固定図式への制限は、元の標的への coslice 射影を厳密に保つ。 -/
lemma sliceUnderRestrict_projection {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    sliceUnderRestrict p f ≫ sliceUnderProjection (f ≫ p) = sliceUnderProjection p := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInr _ _ ≫ (joinMap f (𝟙 _) ≫ s.val)) = _
  rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
