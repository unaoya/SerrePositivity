module

public import Mathlib.Data.Int.Interval

public import SerrePositivity.HomologicalAlgebra.AdicFilteredComplex

/-!
# From graded boundary lifting to acyclicity of an adic tail

A graded evaluation identifies each source component with an adic power in the
target term. Degreewise injectivity reflects closed elements, while lifting a
graded closed element to a boundary gives exactness of the shifted adic tail.
The gradewise image, injectivity, and boundary-lifting hypotheses are explicit;
no exactness or multiplicity theorem is supplied as an unproved input.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.GradedAdicExactness

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable {C P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (NS : ∀ q : ℤ, ℕ → Submodule R (C.X q)) (E : C ⟶ P) (I : Ideal R)
variable (himage : ∀ q k, (NS q k).map (E.f q).hom = I ^ k • ⊤)
variable (hinj : ∀ q k, Set.InjOn (E.f q).hom (NS q k))
variable (hdegree : ∀ q k, ∀ m ∈ NS q k,
  C.d q (q + 1) m ∈ NS (q + 1) (k + 1))

/-- Evaluation commutes with the differential. -/
theorem differential_eval (q r : ℤ) (m : C.X q) :
    P.d q r (E.f q m) = E.f r (C.d q r m) :=
  congrArg (fun f => f m) (E.comm q r)

include himage hdegree in
/-- The degree-zero image is the whole target term, and the differential raises
source degree, so the evaluated differential has entries in `I`. -/
theorem differential_range_le : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤ := by
  intro q
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (NS q 0).map (E.f q).hom := by rw [himage]; simp
  obtain ⟨m, hm, hem⟩ := Submodule.mem_map.mp hx
  have hdm : E.f (q + 1) (C.d q (q + 1) m) ∈ I • (⊤ : Submodule R (P.X (q + 1))) := by
    have h : E.f (q + 1) (C.d q (q + 1) m) ∈
        (NS (q + 1) 1).map (E.f (q + 1)).hom :=
      Submodule.mem_map.mpr ⟨C.d q (q + 1) m, hdegree q 0 m hm, rfl⟩
    rw [himage, pow_one] at h
    exact h
  have hcomm := differential_eval E q (q + 1) m
  rw [hem] at hcomm
  rw [hcomm]
  exact hdm

include himage hinj hdegree in
/-- A closed element of a target adic power lifts to a closed source component. -/
theorem exists_closed_lift (q : ℤ) (k : ℕ) (x : P.X q)
    (hx : x ∈ I ^ k • (⊤ : Submodule R (P.X q))) (hdx : P.d q (q + 1) x = 0) :
    ∃ m : C.X q, m ∈ NS q k ∧ E.f q m = x ∧ C.d q (q + 1) m = 0 := by
  rw [← himage q k] at hx
  obtain ⟨m, hm, hem⟩ := Submodule.mem_map.mp hx
  refine ⟨m, hm, hem, ?_⟩
  apply hinj (q + 1) (k + 1) (hdegree q k m hm) (Submodule.zero_mem _)
  have hcomm := differential_eval E q (q + 1) m
  rw [hem, hdx] at hcomm
  exact hcomm.symm.trans ((E.f (q + 1)).hom.map_zero.symm)

include himage hinj hdegree in
/-- A boundary lift in the graded source becomes a boundary with one lower adic power. -/
theorem exists_adic_boundary (q : ℤ) (k : ℕ)
    (hboundary : ∀ m ∈ NS q k, C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (x : P.X q) (hx : x ∈ I ^ k • (⊤ : Submodule R (P.X q)))
    (hdx : P.d q (q + 1) x = 0) :
    ∃ y : P.X (q - 1), y ∈ I ^ (k - 1) • (⊤ : Submodule R (P.X (q - 1))) ∧
      P.d (q - 1) q y = x := by
  obtain ⟨m, hm, hem, hdm⟩ := exists_closed_lift NS E I himage hinj hdegree q k x hx hdx
  obtain ⟨y, hy, hdy⟩ := hboundary m hm hdm
  refine ⟨E.f (q - 1) y, ?_, ?_⟩
  · rw [← himage]
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  · rw [differential_eval E, hdy, hem]

include hinj in
/-- A high enough shifted adic tail is acyclic, by actual lifting of every closed
element to a boundary in the previous tail term. Boundary lifting is needed only
in the finite range of degrees in which the target can be nonzero. -/
theorem tail_acyclic_of_graded_boundary_lifting_on_interval
    (b h : ℕ)
    (hbounded : ∀ q : ℤ, q < -(h : ℤ) ∨ 0 < q → IsZero (P.X q))
    (hboundary : ∀ q ∈ Finset.Icc (-(h : ℤ)) 0, ∀ k, b ≤ k → 1 ≤ k → ∀ m ∈ NS q k,
      C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (n : ℕ) (hn : b + h + 1 ≤ n) :
    ∀ q : ℤ, IsZero ((AdicFilteredComplex.tail P I
      (differential_range_le NS E I himage hdegree) (n : ℤ)).homology q) := by
  let T := AdicFilteredComplex.tail P I (differential_range_le NS E I himage hdegree) (n : ℤ)
  intro q
  by_cases hq : q < -(h : ℤ) ∨ 0 < q
  · apply isZero_homology_of_isZero_X T q
    let : Subsingleton (P.X q) := ModuleCat.isZero_iff_subsingleton.mp (hbounded q hq)
    change IsZero (ModuleCat.of R (AdicFilteredComplex.term P I (n : ℤ) q))
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  · apply (HomologicalComplex.exactAt_iff_isZero_homology T q).mp
    rw [HomologicalComplex.exactAt_iff' T (q - 1) q (q + 1)
      (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ x : AdicFilteredComplex.term P I (n : ℤ) q,
      T.d q (q + 1) x = 0 → ∃ y : AdicFilteredComplex.term P I (n : ℤ) (q - 1),
        T.d (q - 1) q y = x
    intro x hx
    change T.d q (q + 1) x = 0 at hx
    have hdx : P.d q (q + 1) (x : P.X q) = 0 := congrArg Subtype.val hx
    let k := ((n : ℤ) + q).toNat
    have hk : b ≤ k := by dsimp [k]; omega
    have hkpos : 1 ≤ k := by dsimp [k]; omega
    have hqmem : q ∈ Finset.Icc (-(h : ℤ)) 0 := by
      rw [Finset.mem_Icc]
      omega
    obtain ⟨y, hy, hdy⟩ := exists_adic_boundary NS E I himage hinj hdegree q k
      (hboundary q hqmem k hk hkpos) (x : P.X q) x.2 hdx
    have hprev : ((n : ℤ) + (q - 1)).toNat = k - 1 := by dsimp [k]; omega
    have hyT : y ∈ AdicFilteredComplex.term P I (n : ℤ) (q - 1) := by
      change y ∈ I ^ ((n : ℤ) + (q - 1)).toNat • (⊤ : Submodule R (P.X (q - 1)))
      rwa [hprev]
    refine ⟨⟨y, hyT⟩, ?_⟩
    apply Subtype.ext
    exact hdy

include hinj in
/-- The unrestricted boundary-lifting hypothesis implies the interval version. -/
theorem tail_acyclic_of_graded_boundary_lifting
    (b h : ℕ)
    (hbounded : ∀ q : ℤ, q < -(h : ℤ) ∨ 0 < q → IsZero (P.X q))
    (hboundary : ∀ q k, b ≤ k → 1 ≤ k → ∀ m ∈ NS q k,
      C.d q (q + 1) m = 0 →
      ∃ y : C.X (q - 1), y ∈ NS (q - 1) (k - 1) ∧ C.d (q - 1) q y = m)
    (n : ℕ) (hn : b + h + 1 ≤ n) :
    ∀ q : ℤ, IsZero ((AdicFilteredComplex.tail P I
      (differential_range_le NS E I himage hdegree) (n : ℤ)).homology q) :=
  tail_acyclic_of_graded_boundary_lifting_on_interval NS E I himage hinj hdegree b h hbounded
    (fun q _ => hboundary q) n hn

end SerrePositivity.GradedAdicExactness
