module

public import SerrePositivity.LengthAlgebra.CohenMacaulay
public import SerrePositivity.LengthAlgebra.Comparison
public import SerrePositivity.LengthAlgebra.PerfectMinimalLowerBound

/-! # λ-平坦性を有限射影版の比較・消滅・下界に入力する

Koszul の有限性や消滅を仮定し直さず、有限長加群の Tor 条件から供給する。
長さ零による消滅と Euler 下界の証明は共通の反復錐定理を使う既存の実現に委ねる。
-/

@[expose] public section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits IsLocalRing

open scoped ENNReal

section lower

variable {A C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing C]
  (φ : A →+* C) (lam : NormalizedLength C ((maximalIdeal A).map φ))
  (hfg : ((maximalIdeal A).map φ).FG) {e : ℕ} (z : Fin e → A)
  (hJ : (maximalIdeal A).map φ ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflat : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0)
  (r : ℝ≥0∞) (hr : r ≠ ⊤) (hrank : lam.len (TorAlg φ 0 (A ⧸ maximalIdeal A)) = r)

include hfg hJ hz hreg hflat in
/-- λ-平坦性から有限射影複体の新交叉型消滅へ。有限ランクの仮定は不要。 -/
theorem lambdaHomology_projective_vanishing_of_flat
    (P : CochainComplex (ModuleCat.{u} C) ℤ) (hP : strictlyPerfectComplex C P)
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, Nonempty (Homotopy (smulId (φ (z j) ^ v) P) 0))
    (a b : ℤ) (hbound : ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) : lam.len (P.homology q) = 0 :=
  lambdaHomology_projective_vanishing lam hfg (fun j ↦ φ (z j) ^ v)
    (le_radical_span_pow (φ ∘ z) hJ v)
    (koszulAcyclic_of_flat φ lam z hz hreg hflat v hv) P hP hx a b hbound q hq

/-- λ-平坦な有限ランクの代数上で、極小性から共通 Euler 評価の下界を得る。 -/
theorem perfectEuler_minimal_lower_bound_of_flat
    (P : CochainComplex (ModuleCat.{u} C) ℤ) (hP : strictlyPerfectComplex C P)
    (hs : IsSupported (φ ∘ z) P) (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, Nonempty (Homotopy (smulId (φ (z j) ^ v) P) 0))
    (hbound : ∀ q, q < -(e : ℤ) ∨ 0 < q → IsZero (P.X q))
    (I : Ideal C) (hI : IsPowTorsion ((maximalIdeal A).map φ) (C ⧸ I))
    (b : ℕ) (basis : P.X 0 ≅ ModuleCat.of C (Fin b → C))
    (hmin : ∀ m : P.X (-1), ∀ j, basis.hom.hom ((P.d (-1) 0).hom m) j ∈ I) :
    b * (lam.len (C ⧸ I)).toReal ≤
      perfectEuler lam hfg (φ ∘ z) hJ (koszulFinite_of_flat φ lam z hz hreg hflat r hr hrank)
        ⟨perfectHomotopyObj C P hP, (perfectHomotopyObj_supported_iff _ P hP).mpr hs⟩ :=
  perfectEuler_minimal_lower_bound lam hfg (φ ∘ z) hJ
    (koszulFinite_of_flat φ lam z hz hreg hflat r hr hrank) P hP hs v hx
    (koszulAcyclic_of_flat φ lam z hz hreg hflat v hv) hbound I hI b basis hmin

end lower

section comparison

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing S] [CommRing C] [CommRing D]
  (α : A →+* S) (φ : S →+* C) (ψ : S →+* D)
  (lam : NormalizedLength C ((maximalIdeal A).map (φ.comp α)))
  (mu : NormalizedLength D ((maximalIdeal A).map (ψ.comp α)))
  (hfg : ((maximalIdeal A).map (φ.comp α)).FG)
  (hIfg : ((maximalIdeal A).map (ψ.comp α)).FG)
  {e : ℕ} (z : Fin e → A)
  (hJ : (maximalIdeal A).map (φ.comp α) ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hI : (maximalIdeal A).map (ψ.comp α) ≤ (Ideal.span (Set.range (ψ ∘ α ∘ z))).radical)
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflatC : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg (φ.comp α) i V) = 0)
  (hflatD : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → mu.len (TorAlg (ψ.comp α) i V) = 0)
  (r : ℝ≥0∞) (hr : r ≠ ⊤)
  (hrankC : lam.len (TorAlg (φ.comp α) 0 (A ⧸ maximalIdeal A)) = r)
  (hrankD : mu.len (TorAlg (ψ.comp α) 0 (A ⧸ maximalIdeal A)) = r)

/-- 同じ有限ランクの二つの λ-平坦代数では、降下入力から共役和が一致する。 -/
theorem perfectEuler_conjSum_eq_of_flat
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z)))]
    (hdesc : ∀ y : TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z)),
      (∀ g : G, g • y = y) → ∃ (n : ℕ) (x : TriangulatedK0 (SupportedPerfectHomotopy z)),
        0 < n ∧ n • y = TriangulatedK0.map (supportedPerfectChangeRing α z) x)
    (y : TriangulatedK0 (SupportedPerfectHomotopy (α ∘ z))) :
    ∑ g : G, perfectBaseChangeEulerK0 φ lam hfg (α ∘ z) hJ
      (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC) (g • y) =
    ∑ g : G, perfectBaseChangeEulerK0 ψ mu hIfg (α ∘ z) hI
      (koszulFinite_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD) (g • y) := by
  apply perfectEuler_conjSum_eq α φ ψ lam mu hfg hIfg z hJ hI _ _ hz
    (isKoszulResolution_of_isWeaklyRegular z hreg) _ hdesc y
  exact (koszulEuler_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC).trans
    (koszulEuler_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD).symm

end comparison

end SerrePositivity.LengthAlgebra
