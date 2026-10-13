module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 定義イデアルの冪を含む商と完備化

Iのある冪を含むHについて、完備化のHによる商を元のR/Hへ同定する。
Noether性は不要。評価の核の計算にIの有限生成性だけを用いる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R] (I H : Ideal R) (n : ℕ) (hn : I ^ n ≤ H)

/-- n段評価をHによる商へ送る標準代数写像。 -/
def adicCompletionOpenQuotientMap : AdicCompletion I R →ₐ[R] R ⧸ H :=
  (Ideal.Quotient.factorₐ R hn).comp (AdicCompletion.evalₐ I n)

@[simp] theorem adicCompletionOpenQuotientMap_algebraMap (r : R) :
    adicCompletionOpenQuotientMap I H n hn (algebraMap R (AdicCompletion I R) r) =
      Ideal.Quotient.mk H r := by
  simp [adicCompletionOpenQuotientMap, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of]

/-- 開イデアルによる商への評価は全射。 -/
theorem adicCompletionOpenQuotientMap_surjective :
    Function.Surjective (adicCompletionOpenQuotientMap I H n hn) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap R (AdicCompletion I R) r,
    adicCompletionOpenQuotientMap_algebraMap I H n hn r⟩

/-- 開イデアルによる商への評価の核は、そのイデアルの完備化への拡張。 -/
theorem adicCompletionOpenQuotientMap_ker (hI : I.FG) :
    RingHom.ker (adicCompletionOpenQuotientMap I H n hn).toRingHom =
      H.map (algebraMap R (AdicCompletion I R)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hrH : r ∈ H := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hzero : adicCompletionOpenQuotientMap I H n hn x = 0 := hx
      change (Ideal.Quotient.factorₐ R hn) (AdicCompletion.evalₐ I n x) = 0 at hzero
      rw [← hr] at hzero
      exact hzero
    have hd : x - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
      rw [← adicCompletion_ker_eval_eq_map I hI n]
      change AdicCompletion.evalₐ I n (x - algebraMap R (AdicCompletion I R) r) = 0
      rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
      exact sub_eq_zero.mpr hr.symm
    have hdH := Ideal.map_mono hn hd
    have hrmap := Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) hrH
    simpa using (H.map (algebraMap R (AdicCompletion I R))).add_mem hdH hrmap
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change adicCompletionOpenQuotientMap I H n hn (algebraMap R (AdicCompletion I R) r) = 0
    rw [adicCompletionOpenQuotientMap_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- 完備化してから開イデアルで割ることと、元の環で割ることはR代数として同型。 -/
def adicCompletionOpenQuotientEquiv (hI : I.FG) :
    (AdicCompletion I R ⧸ H.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R] R ⧸ H :=
  (Ideal.quotientEquivAlgOfEq R (adicCompletionOpenQuotientMap_ker I H n hn hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (adicCompletionOpenQuotientMap_surjective I H n hn))

end SerrePositivity
