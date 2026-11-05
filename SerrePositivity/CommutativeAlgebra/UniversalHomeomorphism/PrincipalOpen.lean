module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic

/-!
# 普遍同相の主開集合への制限

## 概要
普遍同相は、始域の元とその像を反転しても普遍同相。

## 方針
一般の局所化の安定性を、冪の分母系の標準同型で主局所化へ移す。

## 規約
結論の射は Mathlib の `Localization.awayMap`。

## 使われ方
有限エタール層別の主開集合の細分。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 全単射な環準同型は普遍同相。 -/
theorem isUniversalHomeomorphism_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) : IsUniversalHomeomorphism f := by
  apply isUniversalHomeomorphism_of_nil_kernel f hf.surjective
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf.injective]
  exact bot_le

/-- 普遍同相を主開集合に制限しても普遍同相。 -/
theorem isUniversalHomeomorphism_awayMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : A) (hf : IsUniversalHomeomorphism f) :
    IsUniversalHomeomorphism (Localization.awayMap f g) := by
  let M := Submonoid.powers g
  let B₀ := Localization (M.map f)
  let B₁ := Localization.Away (f g)
  let : IsLocalization (M.map f) B₁ := by
    rw [Submonoid.map_powers]
    infer_instance
  let e := IsLocalization.algEquiv (M.map f) B₀ B₁
  have he := isUniversalHomeomorphism_of_bijective e.toRingHom e.bijective
  have h := isUniversalHomeomorphism_comp (localizationMap f M) e.toRingHom
    (isUniversalHomeomorphism_localizationMap f M hf) he
  have hmap : e.toRingHom.comp (localizationMap f M) = Localization.awayMap f g := by
    apply IsLocalization.ringHom_ext M
    ext x
    change e (localizationMap f M (algebraMap A (Localization M) x)) = _
    rw [localizationMap_algebraMap]
    simpa only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
      using e.commutes (f x)
  rwa [hmap] at h

end SerrePositivity.CommutativeAlgebra
