module

public import SerrePositivity.HomologicalAlgebra.NullHomotopy
public import SerrePositivity.HomologicalAlgebra.FreeTerms
public import SerrePositivity.CommutativeAlgebra.PowTorsion
public import SerrePositivity.PerfectComplex.Support
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Support

/-!
# ホモロジーの台と台の条件

`HasHomologySupport I P`：各ホモロジー `H^i(P)` の台が `V(I)` に入ること。Noether 環上の有限加群の
複体では `I ≤ √(Ann H^i(P))` と同値で、各次数で `I` のある冪がホモロジーを消す。有界なら共通の冪がとれる。

台の条件 `IsSupported w P`（`w_j^v • 𝟙 P` が零ホモトピック）との関係：

- `IsSupported w P → HasHomologySupport (w) P` は `IsSupported.le_radical_annihilator`
  （`Support.lean`）。
- 逆は、有界な有限射影複体について、ホモロジーを消すスカラーの冪が零ホモトピックであること
  （`HomologicalAlgebra/NullHomotopy.lean`）から出る（`isSupported_of_homologySupport`）。

これで、ホモロジーの台で定義した条件から Lemma 3.5 の要求する `IsPerfectSupported` が得られる
（`isPerfectSupported_of_homologySupport`。`IntersectionMultiplicity/BaseChangeResolution.lean`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- 各ホモロジー `H^i(P)` の台が `V(I)` に入ること。 -/
def HasHomologySupport (I : Ideal T) (P : CochainComplex (ModuleCat.{u} T) ℤ) : Prop :=
  ∀ i, Module.support T (P.homology i) ⊆ PrimeSpectrum.zeroLocus I

variable [IsNoetherianRing T]

/-- 有限加群の複体では、ホモロジーの台の条件は `I ≤ √(Ann H^i(P))` と同値。 -/
lemma homologySupport_iff_le_radical_annihilator (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i)) :
    HasHomologySupport I P ↔ ∀ i, I ≤ (Module.annihilator T (P.homology i)).radical := by
  unfold HasHomologySupport
  apply forall_congr'
  intro i
  have := hfinite i
  have := homology_moduleFinite P i
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]

/-- ホモロジーの台の条件から、各次数で `I` のある冪がホモロジーを消す。 -/
lemma homology_pow_torsion_of_support (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hP : HasHomologySupport I P) (i : ℤ) :
    ∃ n : ℕ, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) :=
  IsPowTorsion.of_le_radical_annihilator I.fg_of_isNoetherianRing
    ((homologySupport_iff_le_radical_annihilator I P hfinite).mp hP i)

/-- 有界なら、すべてのホモロジーを消す共通の冪がとれる。 -/
theorem exists_common_pow_annihilator_of_homologySupport (I : Ideal T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (hfinite : ∀ i, Module.Finite T (P.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport I P) :
    ∃ n : ℕ, ∀ i, Module.IsTorsionBySet T (P.homology i) (I ^ n : Ideal T) := by
  classical
  obtain ⟨a, b, hab⟩ := hbounded
  choose n hn using homology_pow_torsion_of_support I P hfinite hP
  refine ⟨(Finset.Icc a b).sup n, fun i ↦ ?_⟩
  by_cases hi : i ∈ Finset.Icc a b
  · have hpow : I ^ (Finset.Icc a b).sup n ≤ I ^ n i :=
      Ideal.pow_le_pow_right (Finset.le_sup hi)
    intro x r
    exact @hn i x ⟨r, hpow r.property⟩
  · have hz : IsZero (P.homology i) :=
      isZero_homology_of_isZero_X _ _ (hab i (by simp only [Finset.mem_Icc] at hi; omega))
    have := ModuleCat.subsingleton_of_isZero hz
    intro x r
    exact Subsingleton.elim _ _

/-! ## 台の条件との関係 -/

/-- 有界な有限射影複体では、ホモロジーの台の条件から台の条件 `IsSupported` が出る。 -/
theorem isSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsSupported w P := by
  classical
  obtain ⟨n, hn⟩ := exists_common_pow_annihilator_of_homologySupport _ P hfinite hbound hP
  have each : ∀ j, ∃ v : ℕ, Nonempty (Homotopy (w j ^ v • 𝟙 P) 0) := by
    intro j
    have hw : w j ∈ Ideal.span (Set.range w) := Ideal.subset_span (Set.mem_range_self j)
    have hwN : w j ^ n ∈ (Ideal.span (Set.range w)) ^ n := Ideal.pow_mem_pow hw n
    have hr : ∀ i, w j ^ n • 𝟙 (P.homology i) = 0 := by
      intro i
      ext x
      exact @hn i x ⟨w j ^ n, hwN⟩
    obtain ⟨m, hm⟩ := exists_pow_nullHomotopy_of_homology_annihilated P (w j ^ n) hproj hbound hr
    exact ⟨n * m, by simpa only [pow_mul] using hm⟩
  choose v hv using each
  refine ⟨Finset.univ.sup v, fun j ↦ ?_⟩
  have hj : v j ≤ Finset.univ.sup v := Finset.le_sup (Finset.mem_univ j)
  have h := (hv j).some.smul (w j ^ (Finset.univ.sup v - v j))
  rw [smul_zero, ← mul_smul, ← pow_add, Nat.sub_add_cancel hj] at h
  exact ⟨h⟩

/-- 有界な有限射影複体では、二つの台の条件は一致する。 -/
theorem isSupported_iff_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hproj : ∀ i, Projective (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    IsSupported w P ↔ HasHomologySupport (Ideal.span (Set.range w)) P := by
  constructor
  · intro h
    exact (homologySupport_iff_le_radical_annihilator _ P hfinite).mpr
      (h.le_radical_annihilator)
  · exact isSupported_of_homologySupport w P hfinite hproj hbound

/-- 有界な有限自由複体で、ホモロジーの台が `V(w)` に入るものは、`w` に台をもつ完全複体。 -/
theorem isPerfectSupported_of_homologySupport {e : ℕ} (w : Fin e → T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ)
    (hfinite : ∀ i, Module.Finite T (P.X i)) (hfree : ∀ i, Module.Free T (P.X i))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : HasHomologySupport (Ideal.span (Set.range w)) P) : IsPerfectSupported w P where
  bounded := hbound
  free := hfree
  finite := hfinite
  supported := isSupported_of_homologySupport w P hfinite
    (fun i ↦ projective_of_free (hfree i)) hbound hP

end SerrePositivity
