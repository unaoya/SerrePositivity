module

public import SerrePositivity.AlgebraicGeometry.OpenImage

/-!
概要：同型となる開部分に入る底変換は、その全体で同型。
方針：開部分上の同型の底変換を、逆像が全空間であることと合わせる。
規約：逆像が全空間という条件を明示する。
使われ方：中心外の素点での局所化を同型な底変換として扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 全空間への制限が同型なら、元の射も同型。 -/
theorem isIso_of_restrict_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (f ∣_ (⊤ : Y.Opens))] : IsIso f := by
  letI : IsIso (⊤ : Y.Opens).ι := by
    change IsIso Y.topIso.hom
    infer_instance
  letI : IsIso (f ⁻¹ᵁ (⊤ : Y.Opens)).ι := by
    change IsIso X.topIso.hom
    infer_instance
  have h := morphismRestrict_ι f (⊤ : Y.Opens)
  letI : IsIso ((f ⁻¹ᵁ (⊤ : Y.Opens)).ι ≫ f) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (f ⁻¹ᵁ (⊤ : Y.Opens)).ι f

/-- 同型な開部分の逆像が全空間なら、底変換した射は同型。 -/
theorem pullback_snd_isIso_of_open_preimage_top {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (U : S.Opens) [IsIso (f ∣_ U)]
    (hU : g ⁻¹ᵁ U = ⊤) : IsIso (pullback.snd f g) := by
  have h := pullback_snd_restrict_isIso f g U
  rw [hU] at h
  letI := h
  exact isIso_of_restrict_top (pullback.snd f g)

end SerrePositivity.AlgebraicGeometry
