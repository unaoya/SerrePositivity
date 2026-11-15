module

public import SerrePositivity.AlgebraicGeometry.GenericFlatCoefficientFreeChart
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：有限個の一般自由開を、一つの有限生成係数部分代数上へ移す。
方針：極小素点の準コンパクト性で有限化し、係数部分代数の有限 join を取る。
規約：基本開の元と自由性を同じ係数射で移す。
使われ方：指定平坦開を伴う Noether 模型の係数の供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u v

/-- 局所化上の自由性を、係数代数の射に沿って移す。 -/
theorem free_away_tensor_of_algHom
    {A B C S : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing S]
    [Algebra A B] [Algebra A C] [Algebra A S]
    (f : B →ₐ[A] C) (b : B)
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[A] S)] :
    Module.Free (Localization.Away (f b)) (Localization.Away (f b) ⊗[A] S) := by
  let L := Localization.Away b
  let D := Localization.Away (f b)
  let φ : L →ₐ[A] D := IsLocalization.Away.mapₐ L D f b
  let : Algebra L D := φ.toAlgebra
  have : IsScalarTower A L D := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  let : Module.Free D (D ⊗[L] (L ⊗[A] S)) := inferInstance
  exact Module.Free.of_equiv (Algebra.TensorProduct.cancelBaseChange A L D D S).toLinearEquiv

/-- 有限生成部分代数の有限 join は有限生成。 -/
theorem fg_finset_sup_subalgebra
    {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    {ι : Type v} (T : ι → Subalgebra A R) (h : ∀ i, (T i).FG) (s : Finset ι) :
    (s.sup T).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Subalgebra.fg_bot
  | @insert i s hi ih => simpa only [Finset.sup_insert] using (h i).sup ih

/-- 全極小素点を覆う有限個の一般自由開を、同じ有限生成係数部分代数上で実現する。 -/
theorem exists_common_fg_subalgebra_generic_free_charts
    (A R S : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsReduced R] [Algebra A R]
    [CommRing S] [Algebra A S] [Algebra.FiniteType A S]
    (hmin : IsCompact {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R}) :
    ∃ T : Subalgebra A R, T.FG ∧ ∃ (n : ℕ) (t : Fin n → T),
      (∀ i, Module.Free (Localization.Away (t i)) (Localization.Away (t i) ⊗[A] S)) ∧
      ∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R →
        ∃ i, (t i : R) ∉ q.asIdeal := by
  classical
  let I := Σ T : {T : Subalgebra A R // T.FG},
    {t : T.val // Module.Free (Localization.Away t) (Localization.Away t ⊗[A] S)}
  let V (i : I) : Set (PrimeSpectrum R) := PrimeSpectrum.basicOpen (i.2.val : R)
  have hcover : {q : PrimeSpectrum R | q.asIdeal ∈ minimalPrimes R} ⊆ ⋃ i, V i := by
    intro q hq
    obtain ⟨T, hT, t, ht, hfree⟩ :=
      exists_fg_subalgebra_free_basicOpen_at_minimalPrime A R S hq
    exact Set.mem_iUnion.mpr ⟨⟨⟨T, hT⟩, ⟨t, hfree⟩⟩, ht⟩
  obtain ⟨s, hs⟩ := hmin.elim_finite_subcover V
    (fun i ↦ (PrimeSpectrum.basicOpen (i.2.val : R)).isOpen) hcover
  let F (i : I) := i.1.val
  let T := s.sup F
  have hT : T.FG := fg_finset_sup_subalgebra F (fun i ↦ i.1.property) s
  have hle (i : s) : F i.val ≤ T := Finset.le_sup i.property
  let r (i : s) : T := Subalgebra.inclusion (hle i) i.val.2.val
  have hfree (i : s) :
      Module.Free (Localization.Away (r i)) (Localization.Away (r i) ⊗[A] S) := by
    let : Module.Free (Localization.Away i.val.2.val)
      (Localization.Away i.val.2.val ⊗[A] S) := i.val.2.property
    exact free_away_tensor_of_algHom (Subalgebra.inclusion (hle i)) i.val.2.val
  have hcov (q : PrimeSpectrum R) (hq : q.asIdeal ∈ minimalPrimes R) :
      ∃ i : s, (r i : R) ∉ q.asIdeal := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hq)
    obtain ⟨his, hqi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hqi⟩
  let e := Fintype.equivFin s
  refine ⟨T, hT, Fintype.card s, fun i ↦ r (e.symm i), fun i ↦ hfree (e.symm i), ?_⟩
  intro q hq
  obtain ⟨i, hi⟩ := hcov q hq
  exact ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

end SerrePositivity.AlgebraicGeometry
