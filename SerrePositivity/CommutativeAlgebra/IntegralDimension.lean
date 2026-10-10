module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# 整拡大と Krull 次元

単射な整拡大 `A → B` に対して `dim A = dim B` を示す。
Mathlib の素イデアルの鎖の持ち上げ（going-up）と、整拡大における
収縮の狭義単調性を組み合わせる。ネーター性・局所性・有限生成性は不要。

§2 の塔の各段の次元計算に使う一般論であり、塔の定義には依存しない。
零環や無限次元も Mathlib の `ringKrullDim : WithBot ℕ∞` の規約で扱う。
-/

public section

namespace SerrePositivity

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- 整拡大では素イデアルの真の包含が収縮で保たれるため、拡大環の次元は基底環以下である。
この向きには環準同型の単射性は不要。 -/
theorem ringKrullDim_le_of_integral [Algebra.IsIntegral A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
  intro P Q hPQ
  exact Ideal.IsIntegral.under_lt_under (R := A) hPQ

/-- going-up を満たし、素スペクトルへの収縮が全射なら、基底環の次元は拡大環以下である。
各有限鎖の始点を選び、Mathlib の鎖全体の持ち上げ定理を適用する。 -/
theorem ringKrullDim_le_of_goingUp_of_surjective [Algebra.HasGoingUp A B]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    ringKrullDim A ≤ ringKrullDim B := by
  change (⨆ l : LTSeries (PrimeSpectrum A), (l.length : WithBot ℕ∞)) ≤ _
  apply iSup_le
  intro l
  obtain ⟨P, hP⟩ := hsurj l.head
  let : P.asIdeal.LiesOver l.head.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hP.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  change (l.length : WithBot ℕ∞) ≤ ⨆ L : LTSeries (PrimeSpectrum B), (L.length : WithBot ℕ∞)
  rw [← hlen]
  exact le_iSup (fun L : LTSeries (PrimeSpectrum B) ↦ (L.length : WithBot ℕ∞)) L

/-- 単射な整拡大は Krull 次元を保存する。
lying-over で素スペクトルの全射性を得て、going-up と収縮による二つの不等式を合わせる。 -/
theorem ringKrullDim_eq_of_integral_of_injective [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A B)) : ringKrullDim B = ringKrullDim A := by
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  apply le_antisymm (ringKrullDim_le_of_integral A B)
  apply ringKrullDim_le_of_goingUp_of_surjective A B
  intro p
  obtain ⟨P, hP, hp⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver B))
  exact ⟨⟨P, hP⟩, PrimeSpectrum.ext hp.over.symm⟩

end SerrePositivity
