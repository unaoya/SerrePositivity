module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleCover
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
概要：元の射の全射性と開集合上の同型性を、実際の有限ファイバー冪へ渡す。
方針：対角 lift による全射性と、先頭・末尾の Cartesian な帰納を使う。
規約：G3 の表示と同じ wide pullback の base を保持する。
使われ方：射影 F8 を実際の nerve の全ての項に適用するための幾何学的入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Cartesian square の右辺の開上の同型性を、同じ逆像の左辺へ渡す。 -/
theorem isPullback_restrict_left_isIso {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (W : S.Opens) [IsIso (g ∣_ W)] :
    IsIso (a ∣_ f ⁻¹ᵁ W) := by
  have he : a ⁻¹ᵁ (f ⁻¹ᵁ W) = b ⁻¹ᵁ (g ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  have H' := Scheme.Hom.isPullback_resLE H (US := W) (UT := g ⁻¹ᵁ W) (UX := f ⁻¹ᵁ W)
    (UY := a ⁻¹ᵁ (f ⁻¹ᵁ W)) le_rfl le_rfl (by rw [he]; exact (inf_idem _).symm)
  have : IsIso (g.resLE W (g ⁻¹ᵁ W) le_rfl) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using (inferInstance : IsIso (g ∣_ W))
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.of_isPullback H'.flip
      (inferInstance : IsIso (g.resLE W (g ⁻¹ᵁ W) le_rfl)))

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- 元の射の全射性は、同じ有限ファイバー冪の base に成り立つ。 -/
theorem finiteFiberPowerBase_surjective [Surjective f] (n : ℕ) :
    Surjective (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) := by
  let d : X ⟶ widePullback S (fun _ : Fin (n + 1) ↦ X) (fun _ ↦ f) :=
    WidePullback.lift f (fun _ : Fin (n + 1) ↦ 𝟙 X) (by simp)
  have hd : d ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ f) = f :=
    WidePullback.lift_base _ _ _ _
  have : Surjective (d ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ f)) := by
    rw [hd]
    infer_instance
  exact Surjective.of_comp d (WidePullback.base (fun _ : Fin (n + 1) ↦ f))

set_option backward.isDefEq.respectTransparency false in
/-- 元の射の開上の同型性は、同じ有限ファイバー冪の base に成り立つ。 -/
theorem finiteFiberPowerBase_restrict_isIso (W : S.Opens) [IsIso (f ∣_ W)] (n : ℕ) :
    IsIso (WidePullback.base (fun _ : Fin (n + 1) ↦ f) ∣_ W) := by
  induction n with
  | zero =>
    have h : IsIso (((finiteFiberPowerZeroIso f).hom ≫ f) ∣_ W) := by
      rw [morphismRestrict_comp]
      infer_instance
    exact (finiteFiberPowerZeroIso_hom_base f) ▸ h
  | succ n ih =>
    let v := WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ f))
      (fun j : Fin (n + 1) ↦ WidePullback.π (fun _ : Fin (n + 1 + 1) ↦ f) j.succ)
      (fun j ↦ WidePullback.π_arrow (fun _ : Fin (n + 1 + 1) ↦ f) j.succ)
    have : IsIso (v ∣_ (WidePullback.base (fun _ : Fin (n + 1) ↦ f)) ⁻¹ᵁ W) :=
      isPullback_restrict_left_isIso (isPullback_finiteFiberPowerSucc f n) W
    have hv : v ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ f) =
        WidePullback.base (fun _ : Fin (n + 1 + 1) ↦ f) := by
      dsimp only [v]
      exact WidePullback.lift_base _ _ _ _
    rw [← hv, morphismRestrict_comp]
    infer_instance

end SerrePositivity.AlgebraicGeometry
