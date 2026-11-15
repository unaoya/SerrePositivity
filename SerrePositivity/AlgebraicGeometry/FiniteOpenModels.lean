module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
概要：有限個の準コンパクト開の模型を、同じ有限段へそろえる。
方針：既存の開の模型をそれぞれ取り、有限 cone の共通段へ引き戻す。
規約：実際の極限 cone の射影との等式を保持する。
使われ方：G2 のチャートの重なりの開を同じ係数段へ降ろす。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc

/-- 有限個の準コンパクト開は、一つの共通する有限段の準コンパクト開から来る。 -/
theorem exists_finite_opens_model_of_isLimit {ι : Type v} [Finite ι]
    (U : ι → c.pt.Opens) (hU : ∀ a, IsCompact (U a : Set c.pt)) :
    ∃ (i : J) (V : ι → (D.obj i).Opens),
      ∀ a, IsCompact (V a : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V a = U a := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose i V hV heq using fun a ↦ exists_preimage_eq D c hc (U a) (hU a)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let f (a : ι) : j ⟶ i a := (hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)).some
  refine ⟨j, fun a ↦ D.map (f a) ⁻¹ᵁ V a, ?_⟩
  intro a
  refine ⟨QuasiCompact.isCompact_preimage _ (V a).isOpen (hV a), ?_⟩
  rw [← Scheme.Hom.comp_preimage, c.w, heq]

/-- 有限個の準コンパクト開の等式は、一つの共通する後の段で成立する。 -/
theorem exists_finite_open_equalities_of_isLimit {ι : Type v} [Finite ι]
    {i : J} (U V : ι → (D.obj i).Opens)
    (hU : ∀ a, IsCompact (U a : Set (D.obj i)))
    (hV : ∀ a, IsCompact (V a : Set (D.obj i)))
    (heq : ∀ a, c.π.app i ⁻¹ᵁ U a = c.π.app i ⁻¹ᵁ V a) :
    ∃ (j : J) (f : j ⟶ i), ∀ a, D.map f ⁻¹ᵁ U a = D.map f ⁻¹ᵁ V a := by
  choose j f hf using fun a ↦
    exists_map_preimage_eq_map_preimage D c hc (hU a) (hV a) (heq a)
  obtain ⟨k, g, a, ha⟩ := IsCofiltered.wideCospan f
  refine ⟨k, g, ?_⟩
  intro b
  have h := congrArg (fun W ↦ D.map (a b) ⁻¹ᵁ W) (hf b)
  simpa only [← Scheme.Hom.comp_preimage, ← Functor.map_comp, ha] using h

end SerrePositivity.AlgebraicGeometry
