module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# 有限生成イデアルの nil 性の延長

## 概要
局所化後に nil になる有限生成イデアルは、一つの分母を反転した段階で nil になる。

## 方針
生成元ごとの冪零関係の分母を払い、それらの分母の積を選ぶ。

## 規約
結論はイデアルの nilradical への包含。イデアルの冪零性を仮定しない。

## 使われ方
普遍同相を主開集合へ延ばすときの対角イデアルに適用する。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 有限生成イデアルの生成元の冪零関係は、一つの分母を反転すれば成立する。 -/
theorem exists_away_nil_of_localized_nil
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (M : Submonoid R)
    (f : A →ₐ[R] B) [IsLocalizedModule M f.toLinearMap]
    (I : Ideal A) (hI : I.FG) (h_nil : ∀ x ∈ I, IsNilpotent (f x)) :
    ∃ g : M, I.map (algebraMap A (Localization.Away (algebraMap R A g))) ≤
      nilradical (Localization.Away (algebraMap R A g)) := by
  classical
  obtain ⟨s, hs⟩ := hI
  choose n hn using fun x : s ↦ h_nil x (hs ▸ Ideal.subset_span x.property)
  have hex (x : s) : ∃ r : M, algebraMap R A r * (x : A) ^ n x = 0 := by
    obtain ⟨r, hr⟩ := IsLocalizedModule.exists_of_eq (S := M) (f := f.toLinearMap)
      (show f ((x : A) ^ n x) = f 0 by simpa only [map_pow, map_zero] using hn x)
    exact ⟨r, by simpa [Algebra.smul_def] using hr⟩
  choose r hr using hex
  let g : M := ∏ x : s, r x
  refine ⟨g, ?_⟩
  rw [Ideal.map_le_iff_le_comap, ← hs, Ideal.span_le]
  intro x hx
  let i : s := ⟨x, hx⟩
  let A' := Localization.Away (algebraMap R A g)
  have hdvd : (r i : R) ∣ (g : R) :=
    map_dvd M.subtype (Finset.dvd_prod_of_mem r (Finset.mem_univ i))
  have hu : IsUnit (algebraMap A A' (algebraMap R A (r i))) :=
    isUnit_of_dvd_unit
      (map_dvd ((algebraMap A A').comp (algebraMap R A)) hdvd)
      (IsLocalization.Away.algebraMap_isUnit (algebraMap R A g))
  apply mem_nilradical.mpr
  refine ⟨n i, hu.mul_right_eq_zero.mp ?_⟩
  simpa only [map_mul, map_pow, map_zero] using congrArg (algebraMap A A') (hr i)

end SerrePositivity.CommutativeAlgebra
