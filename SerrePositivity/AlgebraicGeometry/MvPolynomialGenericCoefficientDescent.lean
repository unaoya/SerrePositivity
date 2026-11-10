module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
概要：分数体上の多変数多項式は、基底環の一つの非零元を反転した環に係数を取れる。
方針：多変数多項式環の係数局所化から一つの分母を取り出す。
規約：変数集合の有限性は仮定しない。
使われ方：生成ファイバーの超曲面方程式を基底の稠密開に広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

/--
概要：分数体係数の多変数多項式は、基底の一つの主局所化からの係数変更で得られる。
方針：多項式環の局所化で分子と分母を取り、主局所化でその分母を反転する。
規約：基底は整域とする。
使われ方：超曲面模型の方程式を基底の稠密主開へ降ろす。
-/
theorem exists_away_mvPolynomial_map_eq
    {A K σ : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (p : MvPolynomial σ K) :
    ∃ (a : A) (ha : a ∈ A⁰) (q : MvPolynomial σ (Localization.Away a)),
      map (IsLocalization.Away.lift (g := algebraMap A K) a
        (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))) q = p := by
  let M := A⁰.map (C (σ := σ))
  obtain ⟨b, ⟨s, hs⟩, h⟩ := IsLocalization.exists_mk'_eq M p
  obtain ⟨a, ha, rfl⟩ := hs
  let D := Localization.Away a
  let u : Dˣ := (IsLocalization.Away.algebraMap_isUnit (S := D) a).unit
  let j : D →+* K := IsLocalization.Away.lift a (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))
  have hj : j.comp (algebraMap A D) = algebraMap A K :=
    IsLocalization.Away.lift_comp a _
  have hspec : p * C (algebraMap A K a) = map (algebraMap A K) b := by
    rw [← h]
    simpa only [MvPolynomial.algebraMap_def, map_C] using
      IsLocalization.mk'_spec (MvPolynomial σ K) b (⟨C a, ⟨a, ha, rfl⟩⟩ : M)
  have hunit : j (↑u⁻¹ : D) * algebraMap A K a = 1 := by
    have hInv : (↑u⁻¹ : D) * algebraMap A D a = 1 := u.inv_mul
    have hJa : j (algebraMap A D a) = algebraMap A K a := DFunLike.congr_fun hj a
    simpa only [map_mul, map_one, hJa] using congrArg j hInv
  refine ⟨a, ha, map (algebraMap A D) b * C (↑u⁻¹ : D), ?_⟩
  change map j _ = _
  rw [map_mul, map_map, hj, map_C]
  have huK := IsLocalization.map_units K (⟨a, ha⟩ : A⁰)
  apply (huK.map (C (σ := σ))).mul_left_inj.mp
  rw [mul_assoc, ← C_mul, hunit, map_one, mul_one, hspec]

private theorem optionEquivLeft_map
    {A B σ : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (p : MvPolynomial (Option σ) A) :
    optionEquivLeft B σ (map f p) = (optionEquivLeft A σ p).map (map f) := by
  let g := (optionEquivLeft B σ).toRingHom.comp (map f)
  let h := (Polynomial.mapRingHom (map f)).comp (optionEquivLeft A σ).toRingHom
  have he : g = h := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change optionEquivLeft B σ (map f (C a)) = (optionEquivLeft A σ (C a)).map (map f)
      rw [map_C, optionEquivLeft_C, optionEquivLeft_C, Polynomial.map_C, map_C]
    · intro i
      cases i with
      | none =>
        change optionEquivLeft B σ (map f (X none)) =
          (optionEquivLeft A σ (X none)).map (map f)
        rw [map_X, optionEquivLeft_X_none, optionEquivLeft_X_none, Polynomial.map_X]
      | some x =>
        change optionEquivLeft B σ (map f (X (some x))) =
          (optionEquivLeft A σ (X (some x))).map (map f)
        rw [map_X, optionEquivLeft_X_some, optionEquivLeft_X_some, Polynomial.map_C, map_X]
  exact DFunLike.congr_fun he p

/--
概要：指定変数についてモニックな分数体係数の方程式は、モニックな方程式として主開へ降りる。
方針：係数を降ろし、分数体への単射で最高次係数を比較する。
規約：指定変数は変数集合の `none` で表す。
使われ方：基底を縮めた後の超曲面環の平坦性と生成ファイバーへの単射。
-/
theorem exists_away_monic_option_mvPolynomial_map_eq
    {A K σ : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (p : MvPolynomial (Option σ) K) (hp : (optionEquivLeft K σ p).Monic) :
    ∃ (a : A) (ha : a ∈ A⁰) (q : MvPolynomial (Option σ) (Localization.Away a)),
      (optionEquivLeft (Localization.Away a) σ q).Monic ∧
        map (IsLocalization.Away.lift (g := algebraMap A K) a
          (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))) q = p := by
  obtain ⟨a, ha, q, hq⟩ := exists_away_mvPolynomial_map_eq (A := A) p
  refine ⟨a, ha, q, ?_, hq⟩
  let D := Localization.Away a
  let j : D →+* K := IsLocalization.Away.lift a (IsLocalization.map_units K (⟨a, ha⟩ : A⁰))
  have hj₀ (x : A) : j (algebraMap A D x) = algebraMap A K x :=
    IsLocalization.Away.lift_eq a _ x
  have hj : Function.Injective j := by
    refine (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers a) j).mpr ?_
    intro x y
    refine ⟨congrArg j, fun h => congrArg (algebraMap A D) ?_⟩
    exact IsFractionRing.injective A K (by simpa only [hj₀] using h)
  apply Polynomial.monic_of_injective (MvPolynomial.map_injective (σ := σ) j hj)
  change map j q = p at hq
  rwa [← optionEquivLeft_map, hq]

/--
概要：指定変数についてモニックな方程式を持つ超曲面環は基底上で平坦。
方針：指定変数の冪基底で残りの多項式環上自由になり、多項式環は基底上自由。
規約：指定変数は変数集合の `none` で表す。
使われ方：基底上に降ろした模型をその生成ファイバーへ埋め込む。
-/
theorem flat_mvPolynomial_quotient_of_monic_option
    {A σ : Type*} [CommRing A] (p : MvPolynomial (Option σ) A)
    (hp : (optionEquivLeft A σ p).Monic) :
    Module.Flat A (MvPolynomial (Option σ) A ⧸ Ideal.span {p}) := by
  let R := MvPolynomial σ A
  let e := optionEquivLeft A σ
  let I : Ideal (MvPolynomial (Option σ) A) := Ideal.span {p}
  let J : Ideal (Polynomial R) := Ideal.span {e p}
  have hEq : J = I.map e.toRingHom := by
    change Ideal.span {e p} = (Ideal.span {p}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let : Module.Free R (Polynomial R ⧸ J) := hp.free_quotient
  let : Module.Flat A (Polynomial R ⧸ J) := Module.Flat.trans A R _
  exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlg I J e hEq).toLinearEquiv

end SerrePositivity.AlgebraicGeometry
