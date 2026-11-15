module

public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
概要：余極限で一致する有限型な環からの二射を、一つの同じ遷移で一致させる。
方針：Mathlib の一致判定の二遷移を、filtered 性で等しくする。
規約：係数構造と元の射を保持し、遷移に単射性・平坦性を要求しない。
使われ方：B03・B04 の模型の有限個の可換式を共通の後段へそろえる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

/-- 余極限で一致する係数上の二射は、一つの後段への同じ遷移で一致する。 -/
theorem exists_same_stage_ringHom_equality
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (k : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u})
    (α : (Functor.const J).obj k ⟶ F) {D : CommRingCat.{u}} (f : k ⟶ D)
    (c : Cocone F) (hc : IsColimit c) (hf : f.hom.FiniteType)
    {i : J} (a b : D ⟶ F.obj i) (ha : f ≫ a = α.app i) (hb : f ≫ b = α.app i)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app i) :
    ∃ (j : J) (q : i ⟶ j), a ≫ F.map q = b ≫ F.map q := by
  obtain ⟨j, v, w, heq⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
    k F α f c hc hf.essFiniteType a ha b hb hab
  obtain ⟨l, r, hr⟩ := IsFilteredOrEmpty.cocone_maps v w
  refine ⟨l, v ≫ r, ?_⟩
  have H := congrArg (fun z ↦ z ≫ F.map r) heq
  simpa only [Category.assoc, ← Functor.map_comp, hr] using H

end SerrePositivity.AlgebraicGeometry
