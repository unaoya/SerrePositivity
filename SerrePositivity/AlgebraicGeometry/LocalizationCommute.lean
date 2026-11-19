module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
概要：KST §5 のチャート比較に使う二つの局所化の交換。
方針：係数の局所化の後で一元を可逆化する環を、逆順の局所化として同定する。
規約：実際の環準同型について局所化の普遍条件を述べる。
使われ方：標準 blowup チャートの等式検出。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所化写像を一元局所化した写像は、元の分母の像での局所化を実現する。
方針：二つの局所化の交換定理を、係数写像とその一元局所化に適用する。
規約：KST §5、分母の非零因子性は仮定しない。
使われ方：Rees 代数の局所化をチャートの通常の局所化へ移す。
-/
theorem localization_awayMap_isLocalizationMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (M : Submonoid A) (f : A →+* B)
    (hf : M.IsLocalizationMap f) (a : A) :
    (M.map (algebraMap A (Localization.Away a))).IsLocalizationMap
      (Localization.awayMap f a) := by
  let : Algebra A B := f.toAlgebra
  let : IsLocalization M B := (isLocalization_iff_isLocalizationMap _ _).mpr hf
  let : Algebra A (Localization.Away (f a)) :=
    ((algebraMap B (Localization.Away (f a))).comp f).toAlgebra
  let : Algebra (Localization.Away a) (Localization.Away (f a)) :=
    (Localization.awayMap f a).toAlgebra
  let : SMul A (Localization.Away a) :=
    (inferInstance : Algebra A (Localization.Away a)).toSMul
  let : SMul A (Localization.Away (f a)) :=
    (inferInstance : Algebra A (Localization.Away (f a))).toSMul
  let : SMul B (Localization.Away (f a)) :=
    (inferInstance : Algebra B (Localization.Away (f a))).toSMul
  have : IsScalarTower A B (Localization.Away (f a)) :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := Localization.Away (f a)) rfl
  have : IsScalarTower A (Localization.Away a) (Localization.Away (f a)) := by
    apply IsScalarTower.of_algebraMap_eq' (R := A) (S := Localization.Away a)
      (A := Localization.Away (f a))
    ext x
    exact (IsLocalization.map_eq (M := Submonoid.powers a) (S := Localization.Away a)
      (T := Submonoid.powers (f a)) (Q := Localization.Away (f a)) (g := f)
      (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) x).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
      (Localization.Away (f a)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    change IsLocalization.Away (f a) (Localization.Away (f a))
    infer_instance
  exact (isLocalization_iff_isLocalizationMap _ _).mp
    (IsLocalization.commutes (Localization.Away a) B (Localization.Away (f a))
      (Submonoid.powers a) M)

/--
概要：像と等しい分母を明示しても、局所化の交換条件は変わらない。
方針：分母の等式で移送し、一元局所化の交換に帰着する。
規約：KST §5、分母の冪の包含証明も明示する。
使われ方：Rees の中心元の像が標的の中心元に等しい場合。
-/
theorem localization_powers_map_isLocalizationMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (M : Submonoid A) (f : A →+* B)
    (hf : M.IsLocalizationMap f) (a : A) (b : B) (hab : f a = b)
    (hle : Submonoid.powers a ≤ (Submonoid.powers b).comap f) :
    (M.map (algebraMap A (Localization.Away a))).IsLocalizationMap
      (IsLocalization.map (Localization.Away b) f hle :
        Localization.Away a →+* Localization.Away b) := by
  subst b
  exact localization_awayMap_isLocalizationMap M f hf a

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
