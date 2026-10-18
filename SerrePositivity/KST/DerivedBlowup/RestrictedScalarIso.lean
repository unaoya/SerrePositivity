module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionCategory

/-!
概要：KST §3.1 の局所係数単元による複体自己同型を共通基底環へ制限する。
方針：元の局所係数環で scalar 倍と逆 scalar 倍を作り、係数制限関手で送る。
規約：局所係数単元を基底環の scalar と取り違えない。
使われ方：有限重なりの O(m) の推移単元を Hom 自己同型へ変換する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 概要：局所係数単元の scalar 倍による共通基底環上の複体自己同型。
方針：局所係数環上の可逆な scalar 倍を指定係数制限で送る。
規約：KST §3.1。使われ方：捻りの各 Hom での指定自己同型。 -/
def restrictedScalarUnitIso (K : Complex B) (s : Bˣ) :
    (restriction (algebraMap R B)).obj K ≅ (restriction (algebraMap R B)).obj K :=
  (restriction (algebraMap R B)).mapIso {
    hom := (s : B) • 𝟙 K
    inv := ((s⁻¹ : Bˣ) : B) • 𝟙 K
    hom_inv_id := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [s.inv_mul, one_smul]
    inv_hom_id := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [s.mul_inv, one_smul] }

/-- 概要：係数制限後の scalar 自己同型の順射は元の局所 scalar 倍。
方針：係数制限は各次数の元と元の射の関数を保つ。
規約：KST §3.1。使われ方：捻りの乗法整合式を各次数で計算する。 -/
theorem restrictedScalarUnitIso_hom_apply (K : Complex B) (s : Bˣ) (q : ℤ) (z : K.X q) :
    ((restrictedScalarUnitIso R B K s).hom.f q) z = (s : B) • z := rfl

/-- 概要：係数制限後の scalar 自己同型の逆射は元の逆 scalar 倍。
方針：局所係数環で指定した逆射の関数を読む。
規約：KST §3.1。使われ方：逆捻りの各次数での計算。 -/
theorem restrictedScalarUnitIso_inv_apply (K : Complex B) (s : Bˣ) (q : ℤ) (z : K.X q) :
    ((restrictedScalarUnitIso R B K s).inv.f q) z = ((s⁻¹ : Bˣ) : B) • z := rfl

/-- 概要：単元 1 による係数制限後の自己同型は恒等。
方針：scalar 1 と係数制限関手の恒等保存を使う。
規約：KST §3.1。使われ方：捻りの対角条件と零捻り。 -/
theorem restrictedScalarUnitIso_one (K : Complex B) :
    restrictedScalarUnitIso R B K 1 = Iso.refl _ := by
  apply Iso.ext
  change (restriction (algebraMap R B)).map ((1 : B) • 𝟙 K) = 𝟙 _
  rw [one_smul, CategoryTheory.Functor.map_id]

/-- 概要：二つの単元による自己同型の合成は積の単元による自己同型。
方針：局所係数環上の合成の双線形性を使い、係数制限の合成保存で送る。
規約：KST §3.1。使われ方：整数捻りの加法則。 -/
theorem restrictedScalarUnitIso_mul (K : Complex B) (s t : Bˣ) :
    restrictedScalarUnitIso R B K s ≪≫ restrictedScalarUnitIso R B K t =
      restrictedScalarUnitIso R B K (s * t) := by
  apply Iso.ext
  change (restriction (algebraMap R B)).map ((s : B) • 𝟙 K) ≫
      (restriction (algebraMap R B)).map ((t : B) • 𝟙 K) =
    (restriction (algebraMap R B)).map (((s * t : Bˣ) : B) • 𝟙 K)
  rw [← CategoryTheory.Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, smul_smul, Units.val_mul]

/-- 概要：逆単元による自己同型は指定自己同型の逆。
方針：指定した順逆射の定義を比較する。
規約：KST §3.1。使われ方：負の捻りの自己同型。 -/
theorem restrictedScalarUnitIso_inv (K : Complex B) (s : Bˣ) :
    restrictedScalarUnitIso R B K s⁻¹ = (restrictedScalarUnitIso R B K s).symm := by
  apply Iso.ext
  rfl

end SerrePositivity.KST.DerivedBlowup
