module
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedFibers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Monic factorization and prescribed residue roots over absolutely integrally closed rings -/
@[expose] public noncomputable section
universe u
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
