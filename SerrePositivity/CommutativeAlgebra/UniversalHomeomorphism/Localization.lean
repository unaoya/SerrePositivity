module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.PowerClosure
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.Ring

/-!
# p 乗根で閉じた像の局所化

## 概要
環準同型の像が p 乗根で閉じているという条件を局所化へ移す。

## 方針
分子と分母を表示し、局所化での等式を分母の元を掛けた等式に戻す。

## 規約
分母は始域の部分モノイドと、その終域での像を使う。

## 使われ方
普遍同相の p 冪判定で、導手の上の素イデアルにおける局所化に用いる。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.CommutativeAlgebra

variable {A B : Type*} [CommRing A] [CommRing B]

/-- 同じ分母系に沿って局所化した環準同型。 -/
def localizationMap (f : A →+* B) (S : Submonoid A) :
    Localization S →+* Localization (S.map f) :=
  IsLocalization.map _ f (Submonoid.le_comap_map S)

@[simp] theorem localizationMap_mk' (f : A →+* B) (S : Submonoid A) (a : A) (s : S) :
    localizationMap f S (IsLocalization.mk' (Localization S) a s) =
      IsLocalization.mk' (Localization (S.map f)) (f a) (⟨f s, ⟨s, s.property, rfl⟩⟩ : S.map f) :=
  IsLocalization.map_mk' ..

@[simp] theorem localizationMap_algebraMap (f : A →+* B) (S : Submonoid A) (a : A) :
    localizationMap f S (algebraMap A (Localization S) a) =
      algebraMap B (Localization (S.map f)) (f a) := IsLocalization.map_eq ..

/-- 終域の局所化でも分母を始域の元で取れる。 -/
private theorem exists_mk'_map_eq (f : A →+* B) (S : Submonoid A)
    (x : Localization (S.map f)) :
    ∃ (b : B) (s : S),
      IsLocalization.mk' (Localization (S.map f)) b
        (⟨f s, ⟨s, s.property, rfl⟩⟩ : S.map f) = x := by
  obtain ⟨b, ⟨s, hs⟩, hx⟩ := IsLocalization.exists_mk'_eq (S.map f) x
  obtain ⟨s, hs, rfl⟩ := hs
  exact ⟨b, ⟨s, hs⟩, hx⟩

/-- p 乗根に関する像の閉性は、任意の分母系での局所化で保たれる。 -/
theorem rootClosed_localizationMap (p : ℕ) (hp : 0 < p) (f : A →+* B)
    (S : Submonoid A) (hf : ∀ b : B, b ^ p ∈ f.range → b ∈ f.range)
    (x : Localization (S.map f)) (hx : x ^ p ∈ (localizationMap f S).range) :
    x ∈ (localizationMap f S).range := by
  obtain ⟨b, s, rfl⟩ := exists_mk'_map_eq f S x
  obtain ⟨a', ha'⟩ := hx
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq S a'
  rw [localizationMap_mk', ← IsLocalization.mk'_pow] at ha'
  obtain ⟨⟨v, hv⟩, he⟩ := (IsLocalization.eq (S := Localization (S.map f))).mp ha'
  obtain ⟨v, hv, rfl⟩ := hv
  change f v * ((f s) ^ p * f a) = f v * (f t * b ^ p) at he
  have hpow : (f (v * t) * b) ^ p ∈ f.range := by
    refine ⟨(v * t) ^ (p - 1) * v * (s : A) ^ p * a, ?_⟩
    calc
      f ((v * t) ^ (p - 1) * v * (s : A) ^ p * a) =
          f (v * t) ^ (p - 1) * (f v * ((f s) ^ p * f a)) := by
            simp only [map_mul, map_pow]
            ring
      _ = f (v * t) ^ (p - 1) * (f v * (f t * b ^ p)) := by rw [he]
      _ = (f (v * t) ^ (p - 1) * f (v * t)) * b ^ p := by
        rw [map_mul]
        ring
      _ = f (v * t) ^ p * b ^ p := by
        rw [← pow_succ, Nat.sub_add_cancel hp]
      _ = (f (v * t) * b) ^ p := (mul_pow _ _ _).symm
  obtain ⟨c, hc⟩ := hf _ hpow
  refine ⟨IsLocalization.mk' (Localization S) c (⟨v, hv⟩ * t * s), ?_⟩
  rw [localizationMap_mk']
  apply IsLocalization.mk'_eq_of_eq
  change f ((v * t) * s) * b = f s * f c
  rw [hc]
  simp only [map_mul]
  ring

/-- 導手の逆像を局所化したイデアルは、局所化後の導手の逆像に含まれる。 -/
theorem map_comap_conductor_le (f : A →+* B) (S : Submonoid A) :
    ((subringConductor f.range).comap f).map (algebraMap A (Localization S)) ≤
      (subringConductor (localizationMap f S).range).comap (localizationMap f S) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change ∀ x, localizationMap f S (algebraMap A (Localization S) a) * x ∈
    (localizationMap f S).range
  intro x
  obtain ⟨b, s, rfl⟩ := exists_mk'_map_eq f S x
  obtain ⟨c, hc⟩ := ha b
  refine ⟨IsLocalization.mk' (Localization S) c s, ?_⟩
  rw [localizationMap_mk', localizationMap_algebraMap, IsLocalization.mk'_eq_iff_eq_mul,
    mul_assoc, IsLocalization.mk'_spec, ← map_mul, hc]

/-- 局所化の像に属する元の分母を一つ払う。 -/
theorem exists_mul_mem_range_of_localizationMap_mem (f : A →+* B) (S : Submonoid A)
    (b : B) (hb : algebraMap B (Localization (S.map f)) b ∈ (localizationMap f S).range) :
    ∃ s : S, f s * b ∈ f.range := by
  obtain ⟨a', ha'⟩ := hb
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S a'
  rw [localizationMap_mk', IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at ha'
  obtain ⟨⟨v, hv⟩, he⟩ := (IsLocalization.eq_iff_exists (S.map f)
    (Localization (S.map f))).mp ha'
  obtain ⟨v, hv, rfl⟩ := hv
  refine ⟨⟨v, hv⟩ * s, v * a, ?_⟩
  change f (v * a) = f (v * s) * b
  rw [map_mul, he, map_mul]
  ring

/-- 有限個の加群生成元の分母をまとめると、分母系に属する導手の元を得る。 -/
theorem exists_denominator_mem_conductor [Algebra A B] [Module.Finite A B]
    (S : Submonoid A) (hsurj : Function.Surjective (localizationMap (algebraMap A B) S)) :
    ∃ s : S, algebraMap A B s ∈ subringConductor (algebraMap A B).range := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := B)
  choose s hs using fun i : Fin n ↦
    exists_mul_mem_range_of_localizationMap_mem (algebraMap A B) S (v i)
      (hsurj (algebraMap B (Localization (S.map (algebraMap A B))) (v i)))
  refine ⟨∏ i, s i, ?_⟩
  intro b
  have hb : b ∈ Submodule.span A (Set.range v) := hv.symm ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    rw [ht, Submonoid.coe_mul, map_mul]
    have h := (algebraMap A B).range.mul_mem ((algebraMap A B).mem_range_self t) (hs i)
    convert h using 1
    ring
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [mul_add] using (algebraMap A B).range.add_mem ihx ihy
  | smul a x hx ih =>
    have h := (algebraMap A B).range.mul_mem ((algebraMap A B).mem_range_self a) ih
    simpa only [Algebra.smul_def, mul_left_comm] using h

end SerrePositivity.CommutativeAlgebra
