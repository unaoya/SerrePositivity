module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalStructure
public import SerrePositivity.CommutativeAlgebra.LocalResidueLinearMap
public import SerrePositivity.CommutativeAlgebra.Localization.FiniteAlgebraLift
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion

/-! # 絶対整閉な環上の有限エタール代数の分解

## 概要

絶対整閉な環上でモニック多項式は一次式の積に分解し、剰余体で指定した根を持ち上げられるので、絶対整閉な局所環はヘンゼル的である（`henselianLocalRing`）。エタール代数の点は持ち上がり、局所的な絶対整閉環上の有限エタール代数は積に分解する。大域的には、有限個の主開集合で被覆してそれぞれで分解し、悪い主イデアルの外でも有限な分解の被覆を得る。

## 方針

標準エタール代数の場合に点の持ち上げを示してから一般のエタール代数へ移し、局所化した比較を主開集合へ広げる。

## 規約

`henselianLocalRing` は残す。大域的な自明化は主張しない。

## 使われ方

CLMST の almost な比較（悪い主イデアルの外の分解）。
-/

@[expose] public noncomputable section

universe u

section AbsolutelyIntegrallyClosedHenselianPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open Polynomial IsLocalRing

/-- Every monic polynomial splits over the original absolutely integrally closed ring,
without a domain or reducedness hypothesis. -/
theorem IsAbsolutelyIntegrallyClosed.monic_splits
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (P : R[X]) (hP : P.Monic) : P.Splits := by
  rcases subsingleton_or_nontrivial R with hzero | hnontrivial
  · have hpzero : P = 0 := Subsingleton.elim _ _
    rw [hpzero]
    exact Polynomial.Splits.zero
  suffices ∀ n : ℕ, ∀ Q : R[X], Q.natDegree = n → Q.Monic → Q.Splits by
    exact this P.natDegree P rfl hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q hn hQ
    by_cases hz : n = 0
    · exact Polynomial.Splits.of_natDegree_eq_zero (hn.trans hz)
    obtain ⟨x, hx⟩ := hR Q hQ (hn ▸ Nat.pos_of_ne_zero hz)
    obtain ⟨U, hU⟩ := (Polynomial.dvd_iff_isRoot.mpr hx)
    have hmonic : U.Monic := (monic_X_sub_C x).of_mul_monic_left (hU ▸ hQ)
    have hdeg : U.natDegree < n := by
      have hd : n = 1 + U.natDegree := by
        rw [← hn, hU, (monic_X_sub_C x).natDegree_mul hmonic, natDegree_X_sub_C]
      omega
    rw [hU]
    exact (Polynomial.Splits.X_sub_C x).mul (ih U.natDegree hdeg U rfl hmonic)

/-- Any specified root after mapping to a field lifts to a root of the same original
monic polynomial. The field map need not be surjective. -/
theorem IsAbsolutelyIntegrallyClosed.lift_root_to_field
    {R K : Type u} [CommRing R] [Field K] (hR : IsAbsolutelyIntegrallyClosed R)
    (f : R →+* K) (P : R[X]) (hP : P.Monic) (a₀ : K)
    (ha₀ : P.eval₂ f a₀ = 0) : ∃ a : R, P.IsRoot a ∧ f a = a₀ := by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp (hR.monic_splits P hP)
  rw [hP.leadingCoeff, C_1, one_mul] at hm
  have hz : (m.map (fun a : R => a₀ - f a)).prod = 0 := by
    simpa only [hm, Polynomial.eval₂_multiset_prod, Multiset.map_map,
      eval₂_sub, eval₂_X, eval₂_C, Function.comp_def] using ha₀
  obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hz)
  refine ⟨a, ?_, (sub_eq_zero.mp ha0).symm⟩
  change P.eval a = 0
  rw [hm, Polynomial.eval_multiset_prod]
  apply Multiset.prod_eq_zero
  exact Multiset.mem_map.mpr ⟨X - C a, Multiset.mem_map.mpr ⟨a, ha, rfl⟩, by simp⟩

/-- A local absolutely integrally closed ring is Henselian for its original maximal ideal. -/
theorem IsAbsolutelyIntegrallyClosed.henselianLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsAbsolutelyIntegrallyClosed R) :
    HenselianLocalRing R := by
  refine { (inferInstance : IsLocalRing R) with is_henselian := ?_ }
  intro P hP a₀ ha₀ _hder
  have hz : P.eval₂ (residue R) (residue R a₀) = 0 := by
    rw [Polynomial.eval₂_at_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha₀
  obtain ⟨a, ha, hf⟩ := hR.lift_root_to_field (residue R) P hP (residue R a₀) hz
  refine ⟨a, ha, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change residue R (a - a₀) = 0
  rw [map_sub, hf, sub_self]

/-- A specified residue solution of a standard étale pair lifts to the original local ring. -/
theorem IsAbsolutelyIntegrallyClosed.standardEtale_hasMap_lift
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (P : StandardEtalePair R) (x₀ : ResidueField R) (hx₀ : P.HasMap x₀) :
    ∃ x : R, P.HasMap x ∧ residue R x = x₀ := by
  have hroot : P.f.eval₂ (residue R) x₀ = 0 := hx₀.1
  obtain ⟨x, hx, hres⟩ := hR.lift_root_to_field (residue R) P.f P.monic_f x₀ hroot
  have hunit : IsUnit (P.g.aeval x) := by
    apply isUnit_of_map_unit (residue R)
    have he : residue R (P.g.aeval x) = P.g.aeval x₀ := by
      change residue R (P.g.eval x) = P.g.eval₂ (residue R) x₀
      rw [← Polynomial.eval₂_at_apply, hres]
    rw [he]
    exact hx₀.2
  exact ⟨x, ⟨by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, IsRoot] using hx,
    hunit⟩, hres⟩

/-- A residue-field point of a standard étale algebra lifts to an actual algebra
map to the original base, retaining its specified residue point. -/
theorem IsAbsolutelyIntegrallyClosed.standardEtale_point_lift
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (P : StandardEtalePair R) (point : P.Ring →ₐ[R] ResidueField R) :
    ∃ l : P.Ring →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp l = point := by
  obtain ⟨x, hx, hres⟩ := hR.standardEtale_hasMap_lift P (point P.X) (P.hasMap_X.map point)
  refine ⟨P.lift x hx, ?_⟩
  apply P.hom_ext
  change residue R (P.lift x hx P.X) = point P.X
  rw [P.lift_X]
  exact hres

/-- The same lifting applies to any specified standard étale presentation. -/
theorem IsAbsolutelyIntegrallyClosed.isStandardEtale_point_lift
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Algebra.IsStandardEtale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (point : A →ₐ[R] ResidueField R) :
    ∃ l : A →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp l = point := by
  let P : StandardEtalePresentation R A := Nonempty.some inferInstance
  obtain ⟨l, hl⟩ := hR.standardEtale_point_lift P.P
    (point.comp P.equivRing.symm.toAlgHom)
  refine ⟨l.comp P.equivRing.toAlgHom, ?_⟩
  ext a
  have ha := AlgHom.congr_fun hl (P.equivRing a)
  change (Algebra.ofId R (ResidueField R)) (l (P.equivRing a)) =
    point (P.equivRing.symm (P.equivRing a)) at ha
  rw [AlgEquiv.symm_apply_apply] at ha
  exact ha

/-- Every specified residue-field point of an étale algebra lifts to the original
local absolutely integrally closed base. The lift is an actual algebra map. -/
theorem IsAbsolutelyIntegrallyClosed.etale_point_lift
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (point : A →ₐ[R] ResidueField R) :
    ∃ l : A →ₐ[R] R, (Algebra.ofId R (ResidueField R)).comp l = point := by
  let q := RingHom.ker point.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime point.toRingHom
  obtain ⟨t, ht, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  letI := hstd
  have hunit : IsUnit (point t) := by
    apply isUnit_iff_ne_zero.mpr
    exact ht
  let pointLoc : Localization.Away t →ₐ[R] ResidueField R :=
    IsLocalization.Away.liftAlgHom t hunit
  obtain ⟨l, hl⟩ := hR.isStandardEtale_point_lift pointLoc
  refine ⟨l.comp (IsScalarTower.toAlgHom R A (Localization.Away t)), ?_⟩
  ext a
  have ha := AlgHom.congr_fun hl (algebraMap A (Localization.Away t) a)
  change (Algebra.ofId R (ResidueField R)) (l (algebraMap A (Localization.Away t) a)) =
    pointLoc (algebraMap A (Localization.Away t) a) at ha
  exact ha.trans (IsLocalization.Away.lift_eq t hunit a)

end SerrePositivity

end AbsolutelyIntegrallyClosedHenselianPart

section AbsolutelyIntegrallyClosedEtalePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open IsLocalRing
open scoped TensorProduct

/-- Lift all coordinates of the original finite étale fiber simultaneously.
The resulting map to a finite product is an actual algebra equivalence. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_local_exists_algEquiv
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ r : ℕ, Nonempty (A ≃ₐ[R] (Fin r → R)) := by
  classical
  let K := ResidueField R
  have hfiber : ∃ r : ℕ, Nonempty (K ⊗[R] A ≃ₐ[K] (Fin r → K)) :=
    hR.finiteEtale_residueFiber_exists_algEquiv (maximalIdeal R) A
  obtain ⟨r, ⟨e⟩⟩ := hfiber
  let point (i : Fin r) : A →ₐ[R] K :=
    (((Pi.evalAlgHom K (fun _ : Fin r => K) i).comp e.toAlgHom).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
  have hlift (i : Fin r) : ∃ l : A →ₐ[R] R,
      (Algebra.ofId R K).comp l = point i := hR.etale_point_lift (point i)
  choose l hl using hlift
  let F : A →ₐ[R] (Fin r → R) := AlgHom.pi l
  let q := TensorProduct.piScalarRight R K K (Fin r)
  have hcomm (z : K ⊗[R] A) : q (F.toLinearMap.lTensor K z) = e z := by
    induction z using TensorProduct.inductionOn with
    | tmul k a =>
      ext i
      have hi := AlgHom.congr_fun (hl i) a
      change residue R (l i a) = e ((1 : K) ⊗ₜ[R] a) i at hi
      change (l i a) • k = e (k ⊗ₜ[R] a) i
      rw [Algebra.smul_def]
      change residue R (l i a) * k = e (k ⊗ₜ[R] a) i
      rw [hi]
      have hk : k ⊗ₜ[R] a = k • ((1 : K) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hbij : Function.Bijective (F.toLinearMap.lTensor K) := by
    constructor
    · intro x y hxy
      apply e.injective
      rw [← hcomm, ← hcomm, hxy]
    · intro y
      obtain ⟨x, hx⟩ := e.surjective (q y)
      refine ⟨x, q.injective ?_⟩
      rw [hcomm, hx]
  exact ⟨r, ⟨AlgEquiv.ofBijective F
    (localLinearMap_bijective_of_residue_bijective F.toLinearMap hbij)⟩⟩

/-- Over the original localization at any prime, the actual scalar-extended finite
étale algebra is a finite product of that same local base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_localized_exists_algEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ r : ℕ, Nonempty ((Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p)) :=
  (hR.localization p.primeCompl (Localization.AtPrime p)).finiteEtale_local_exists_algEquiv

/-- All coordinates of the actual stalk splitting descend to one principal neighborhood,
as an algebra map with exactly the specified stalk values. Bijectivity on the principal
neighborhood is the subsequent isomorphism-locus step. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_comparison
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] (hR : IsAbsolutelyIntegrallyClosed R)
    (p : Ideal R) [p.IsPrime] :
    ∃ (r : ℕ) (d : R) (hd : d ∉ p) (ψ : A →ₐ[R] (Fin r → Localization.Away d))
      (e : (Localization.AtPrime p) ⊗[R] A ≃ₐ[Localization.AtPrime p]
        (Fin r → Localization.AtPrime p)),
      ∀ a i, IsLocalization.Away.liftAlgHom d (f := Algebra.ofId R (Localization.AtPrime p))
        (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p) ⟨d, hd⟩) (ψ a i) =
          e ((1 : Localization.AtPrime p) ⊗ₜ[R] a) i := by
  letI : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨r, ⟨e⟩⟩ := hR.finiteEtale_localized_exists_algEquiv (A := A) p
  let φ : A →ₐ[R] (Fin r → Localization.AtPrime p) :=
    (e.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] (Localization.AtPrime p) ⊗[R] A)
  obtain ⟨d, hd, ψ, hψ⟩ := finiteAlgebra_exists_away_lift_pi p.primeCompl
    (Localization.AtPrime p) r φ
  exact ⟨r, d, hd, ψ, e, hψ⟩

end SerrePositivity

end AbsolutelyIntegrallyClosedEtalePart

section AbsolutelyIntegrallyClosedEtaleCoverPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]

/-- At every original prime the actual finite étale algebra splits on a principal
neighborhood into a finite product of the same localized base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_principal_algEquiv
    (hR : IsAbsolutelyIntegrallyClosed R) (p : Ideal R) [p.IsPrime] :
    ∃ g : R, g ∉ p ∧ ∃ r : ℕ,
      Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g)) := by
  letI : Module.FinitePresentation R A := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨r, d, hd, ψ, e, hψ⟩ := hR.finiteEtale_exists_principal_comparison (A := A) p
  obtain ⟨g, hg, _hdg, E, _hE⟩ := principalAlgebraComparison_exists_algEquiv p d hd r ψ e hψ
  exact ⟨g, hg, r, ⟨E⟩⟩

/-- The original principal opens carrying an algebra splitting cover the whole base. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_principalSplitting_span_eq_top
    (hR : IsAbsolutelyIntegrallyClosed R) :
    Ideal.span {g : R | ∃ r : ℕ,
      Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
        (Fin r → Localization.Away g))} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  letI := hm
  obtain ⟨g, hgm, r, e⟩ := hR.finiteEtale_exists_principal_algEquiv (A := A) m
  exact hgm (hle (Ideal.subset_span ⟨r, e⟩))

/-- One finite principal cover suffices, with an actual splitting on every member.
The ranks may vary between members; no constant-rank assumption is introduced. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_exists_finite_principal_cover
    (hR : IsAbsolutelyIntegrallyClosed R) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ g ∈ t, ∃ r : ℕ,
        Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
          (Fin r → Localization.Away g)) := by
  classical
  let U : Set R := {g : R | ∃ r : ℕ,
    Nonempty ((Localization.Away g) ⊗[R] A ≃ₐ[Localization.Away g]
      (Fin r → Localization.Away g))}
  have hU : Ideal.span U = ⊤ := hR.finiteEtale_principalSplitting_span_eq_top (A := A)
  obtain ⟨t, htU, ht⟩ := (Ideal.span_eq_top_iff_finite U).mp hU
  exact ⟨t, ht, fun g hg => htU hg⟩

end SerrePositivity

end AbsolutelyIntegrallyClosedEtaleCoverPart

section AbsolutelyIntegrallyClosedEtaleAwayCoverPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open scoped TensorProduct

/-- Finite étaleness away from the original g supplies an actual finite splitting
cover there. Its original scaled numerators cover D(g), witnessed by one power of g. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtaleAway_exists_finite_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∀ f ∈ t, ∃ r : ℕ,
          Nonempty ((Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))) ∧
        ∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1)) := by
  letI := GenericEtale.awayAlgebra R A g
  intro hetale
  letI := hetale
  letI : Module.Finite (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    GenericEtale.finite_away R A g
  obtain ⟨t, ht, hsplit⟩ := (hR.localization (Submonoid.powers g) (Localization.Away g)).finiteEtale_exists_finite_principal_cover
    (A := Localization.Away (algebraMap R A g))
  exact ⟨t, ht, hsplit, exists_pow_mem_span_scaled_cover_numerators g t ht⟩

end SerrePositivity

end AbsolutelyIntegrallyClosedEtaleAwayCoverPart
