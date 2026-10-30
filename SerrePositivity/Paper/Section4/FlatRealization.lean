module

public import SerrePositivity.LengthAlgebra.CohenMacaulay
public import SerrePositivity.LengthAlgebra.Comparison
public import SerrePositivity.LengthAlgebra.SerreQuotient
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import SerrePositivity.LengthAlgebra.PerfectVanishing
public import SerrePositivity.PerfectComplex.MinimalLowerBound
public import SerrePositivity.Paper.Section4.SymmetricComparison
public import SerrePositivity.Asymptotic.PaperMinimalLowerBound
public import SerrePositivity.Asymptotic.PaperVanishing

/-! # λ-平坦性からランク無視版の比較・下界へ

有限版と同じ `koszulFinite_of_flat`・`koszulAcyclic_of_flat`・`koszulEuler_of_flat`
を実際のランク商の評価へ入力する。列の成長条件、支持、極小性、降下は独立に受け取る。
-/

@[expose] public section
universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotic LengthAlgebra

open scoped ENNReal

section lower

variable {A S C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C]
  (α : A →+* S) (φ : S →+* C) (lam : NormalizedLength C ((maximalIdeal A).map (φ.comp α)))
  (hfg : ((maximalIdeal A).map (φ.comp α)).FG) {e : ℕ} (z : Fin e → A)
  (hJ : (maximalIdeal A).map (φ.comp α) ≤ (Ideal.span (Set.range (φ ∘ α ∘ z))).radical)
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflat : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg (φ.comp α) i V) = 0)
  (r : ℝ≥0∞) (hr : r ≠ ⊤) (hrank : lam.len (TorAlg (φ.comp α) 0 (A ⧸ maximalIdeal A)) = r)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- λ-平坦性から、ランク商のホモロジーが指定された範囲外で零対象となる。 -/
theorem paperBaseChangeHomology_vanishing_of_flat
    (K : CochainComplex (FreeSequence S s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (α ∘ z) ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, α (z j) ^ v • 𝟙 ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((paperBaseChangeHomology φ (α ∘ z) lam hfg hJ
      (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs q).obj
      ⟨(paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK), h⟩) :=
  paperBaseChangeHomology_vanishing φ (α ∘ z) lam hfg hJ
    (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs K hK h v hv hx
    (koszulAcyclic_of_flat (φ.comp α) lam z hz hreg hflat v hv) a b hbound q hq

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- 有限長加群の Tor 条件からランク商の消滅・極小 Euler 下界へ接続する。 -/
theorem paperBaseChangeEuler_minimal_lower_bound_of_flat
    (K : CochainComplex (FreeSequence S s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (α ∘ z) ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, α (z j) ^ v • 𝟙 ((paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK)) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal S) (Q : Ideal C) (hIQ : ∀ a ∈ I, φ a ∈ Q)
    (hQ : IsPowTorsion ((maximalIdeal A).map (φ.comp α)) (C ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → S) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, α (z j) ^ v ∈ I) :
    (lam.len (C ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ
        (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs
        (TriangulatedK0.mk ⟨(paperSequenceFunctor S s).obj (sequenceHomotopyObj K hK), h⟩) :=
  paperBaseChangeEuler_minimal_lower_bound φ (α ∘ z) lam hfg hJ
    (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflat r hr hrank) U hU hs K hK h v hv hx
    (koszulAcyclic_of_flat (φ.comp α) lam z hz hreg hflat v hv) hbound I Q hIQ hQ hmin hzI

end lower

section comparison

variable {A S C D : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [HasDerivedCategory (ModuleCat.{u} A)]
  [CommRing S] [Nontrivial S] [CommRing C] [Nontrivial C] [CommRing D] [Nontrivial D]
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
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二段階の係数変更とランク商の評価の依存型を比較するため。
/-- 同じ有限ランクの λ-平坦代数の評価は、ランク商でも共役和が一致する。 -/
theorem symmetricPaperEuler_conjSum_eq_of_flat
    {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G (TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory)]
    (hdesc : ∀ y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory,
      (∀ g : G, g • y = y) → ∃ (n : ℕ)
        (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing α z) x)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (α ∘ z)).FullSubcategory) :
    ∑ g : G, paperBaseChangeEulerK0 φ (α ∘ z) lam hfg hJ
      (koszulFinite_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC) U hU hs (g • y) =
    ∑ g : G, paperBaseChangeEulerK0 ψ (α ∘ z) mu hIfg hI
      (koszulFinite_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD) U hU hs (g • y) := by
  apply symmetricPaperEuler_conjSum_eq α φ ψ lam mu hfg hIfg z hJ hI _ _ hz
    (isKoszulResolution_of_isWeaklyRegular z hreg) U hU hs _ hdesc y
  exact (koszulEuler_of_flat (φ.comp α) lam z hz hreg hflatC r hr hrankC).trans
    (koszulEuler_of_flat (ψ.comp α) mu z hz hreg hflatD r hr hrankD).symm

end comparison

end SerrePositivity.Section4
