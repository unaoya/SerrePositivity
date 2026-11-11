module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.FiniteType

/-!
概要：分数体に含まれる有限型部分代数は、一つの元を反転した部分代数に含まれる。
方針：有限個の生成元の分母の積を取る。
規約：局所化を分数体の部分代数として表す。
使われ方：同じ関数体を持つアフィン環と超曲面模型の共通の主開を作る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped nonZeroDivisors

/--
概要：分数体の有限型部分代数は、分数体を定める整域のある主局所化に含まれる。
方針：有限個の生成元を共通の分母で表す。
規約：有限型性は整域と両立する共通の基底環上で仮定する。
使われ方：双有理なアフィン模型の比較。
-/
theorem exists_nonzero_le_fractionField_away_of_finiteType
    {A B K : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    (S : Subalgebra A K) [Algebra.FiniteType A S] :
    ∃ (b : B) (hb : b ≠ 0),
      S ≤ (Localization.subalgebra.ofField K (Submonoid.powers b)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hb)).restrictScalars A := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := S)
  choose num den hden heq using fun j : s => IsFractionRing.div_surjective B (j.1 : K)
  let b : B := ∏ j : s, den j
  have hb : b ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => mem_nonZeroDivisors_iff_ne_zero.mp (hden j)
  refine ⟨b, hb, ?_⟩
  let U := (Localization.subalgebra.ofField K (Submonoid.powers b)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb)).restrictScalars A
  have hGen : (s : Set S) ⊆ U.comap S.val := by
    intro x hx
    let j : s := ⟨x, hx⟩
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem den (Finset.mem_univ j)
    have hr' : b = den j * r := hr
    have hne : r ≠ 0 := fun h => hb (by rw [hr', h, mul_zero])
    have hne' : algebraMap B K r ≠ 0 :=
      fun h => hne ((IsFractionRing.injective B K) (h.trans (map_zero _).symm))
    change ∃ (a t : B) (_ : t ∈ Submonoid.powers b),
      (x : K) = algebraMap B K a * (algebraMap B K t)⁻¹
    refine ⟨num j * r, b, Submonoid.mem_powers b, ?_⟩
    rw [← div_eq_mul_inv, hr', map_mul, map_mul, mul_div_mul_right _ _ hne']
    exact (heq j).symm
  have hle : Algebra.adjoin A (s : Set S) ≤ U.comap S.val := Algebra.adjoin_le hGen
  rw [hs] at hle
  intro x hx
  exact hle (show (⟨x, hx⟩ : S) ∈ (⊤ : Subalgebra A S) from by simp)

end SerrePositivity.AlgebraicGeometry
