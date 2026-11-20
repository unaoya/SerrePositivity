module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!
概要：KST §5、Stacks 080Y の中心の admissible 性の移送に使う開集合の逆像の順序。
方針：同型となる開集合上の全射性で逆像の包含を基底へ戻す。
規約：開集合の稠密性や基底全体の全射性は要求しない。
使われ方：降下中心が U を避けることの判定。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：V 上で同型な射は、V に含まれる開集合 U 上でも同型。
方針：V へ制限した射をさらに制限し、一回の制限との同型で移す。
規約：KST §5、Stacks 080Y、二つの開集合の包含を明示する。
使われ方：中心外同型を指定された admissible 開集合へ制限する。
-/
theorem isIso_restrict_of_open_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) [IsIso (f ∣_ V)] (hUV : U ≤ V) : IsIso (f ∣_ U) := by
  let W := V.ι ⁻¹ᵁ U
  have h : IsIso ((f ∣_ V) ∣_ W) := inferInstance
  change (MorphismProperty.isomorphisms Scheme) ((f ∣_ V) ∣_ W) at h
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V W)] at h
  have he : V.ι ''ᵁ W = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  change IsIso (f ∣_ V.ι ''ᵁ W) at h
  rwa [he] at h

set_option backward.isDefEq.respectTransparency false in
/--
概要：U 上で同型な射では、U の逆像から W の逆像への包含は U ⊆ W を意味する。
方針：U 上の点を制限した射の全射性で持ち上げる。
規約：KST §5、Stacks 080Y、基底全体の全射性を仮定しない。
使われ方：blowup 上の中心外条件を元の基底へ降ろす。
-/
theorem open_le_of_preimage_le_of_restrict_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U W : Y.Opens) [IsIso (f ∣_ U)] (h : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ W) : U ≤ W := by
  intro x hx
  obtain ⟨y, hy⟩ := (asIso (f ∣_ U)).hom.homeomorph.surjective ⟨x, hx⟩
  change (f ∣_ U) y = ⟨x, hx⟩ at hy
  have hyx : f y.1 = x := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hy
  have hyW : f y.1 ∈ W := h y.2
  exact hyx ▸ hyW

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
