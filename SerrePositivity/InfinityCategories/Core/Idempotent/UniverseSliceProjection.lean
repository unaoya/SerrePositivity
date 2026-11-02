module

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.UniverseJoin
public import SerrePositivity.InfinityCategories.Core.UniverseJoinNaturality
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.UniverseSlices

/-!
概要：元の slice の宇宙比較と固定図式の制限は、元の射影と厳密に可換。
方針：可変標準単体の左包含と実錐写像の宇宙比較を全次数で照合する。
規約：元の図式と全単体を保持し、点での対応だけで代用しない。
使われ方：持ち上げた元の左 Kan 添字の pullback の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 錐の宇宙比較は、元の可変単体の左包含も標準単体の同型を介して保つ。 -/
lemma idemUniverseConeShapeIso_inl (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[n] : SSet.{u}) K) ≫
      (uliftConeShapeIso K n).hom =
    (uliftStdSimplexIso n).hom ≫
      joinInl (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) := by
  unfold uliftConeShapeIso
  simp only [Iso.trans_hom, joinIso, ← Category.assoc, uliftJoinIso_inl, joinInl_joinMap]

/-- 逆向きの元の錐形状比較も可変単体の左包含を保つ。 -/
lemma idemUniverseConeShapeIso_inv_inl (K : SSet.{u}) (n : ℕ) :
    joinInl (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
      (uliftConeShapeIso K n).inv =
    (uliftStdSimplexIso n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinInl (Δ[n] : SSet.{u}) K) := by
  apply (cancel_mono (uliftConeShapeIso K n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    idemUniverseConeShapeIso_inl, Iso.inv_hom_id_assoc]

/-- 元の全 slice の宇宙比較は、元の標的への射影を厳密に保つ。 -/
lemma idemUniverseSliceOverIso_projection {K X : SSet.{u}} (p : K ⟶ X) :
    (uliftSliceOverIso.{u, v} p).hom ≫
      sliceOverProjection ((SSet.uliftFunctor.{v, u}).map p) =
    (SSet.uliftFunctor.{v, u}).map (sliceOverProjection p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  change SSet.yonedaEquiv (joinInl _ _ ≫
      ((uliftConeShapeIso K n).inv ≫ (SSet.uliftFunctor.{v, u}).map s.val)) =
    ULift.up (SSet.yonedaEquiv (joinInl (Δ[n] : SSet.{u}) K ≫ s.val))
  rw [← Category.assoc, idemUniverseConeShapeIso_inv_inl, Category.assoc,
    ← Functor.map_comp]
  have h := uliftYonedaMap.{u, v} (SSet.yonedaEquiv (joinInl (Δ[n] : SSet.{u}) K ≫ s.val))
  rw [Equiv.symm_apply_apply] at h
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 元の固定図式への制限は、元の標的への slice 射影を厳密に保つ。 -/
lemma idemSliceOverRestrict_projection {K₀ K X : SSet.{u}} (p : K ⟶ X) (f : K₀ ⟶ K) :
    sliceOverRestrict p f ≫ sliceOverProjection (f ≫ p) = sliceOverProjection p := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInl _ _ ≫ (joinMap (𝟙 _) f ≫ s.val)) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
