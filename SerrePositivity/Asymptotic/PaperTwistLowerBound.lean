module

public import SerrePositivity.Asymptotic.PaperMinimalLowerBound
public import SerrePositivity.Asymptotic.PaperTwist
public import SerrePositivity.LengthAlgebra.Koszul

/-! # K₀ のひねりと係数変更の合成、共役ごとの Euler 下界

支持圏の実際の群作用を、係数写像の合成として計算する。
パラメータは固定されるので、Koszul 有限性・消滅は元の条件をそのまま使える。
長さの群不変性は使わず、極小性による共通の下界を各共役に適用する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

section composition

variable {R S T : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  [CommRing T] [Nontrivial T] {s : ℕ → ℕ} (σ : R →+* S) (φ : S →+* T)
  {e : ℕ} (z : Fin e → R) (w : Fin e → S) (hw : σ ∘ z = w)
  {J : Ideal T} (lam : NormalizedLength T J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ w))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (φ ∘ w))
  (hJ' : J ≤ (Ideal.span (Set.range ((φ.comp σ) ∘ z))).radical)
  (hfin' : LengthAlgebra.KoszulFinite lam ((φ.comp σ) ∘ z))
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 指定したパラメータの移送と、二段階の係数変更の型の比較に必要。
/-- 支持の指定を保つ写像の後の Euler 評価は、合成した係数写像による評価に等しい。 -/
theorem paperBaseChangeEulerK0_comp_to
    (y : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory) :
    paperBaseChangeEulerK0 φ w lam hfg hJ hfin U hU hs
      (paperSupportedMap σ z w hw y) =
    paperBaseChangeEulerK0 (φ.comp σ) z lam hfg hJ' hfin' U hU hs y := by
  subst w
  have hc := DFunLike.congr_fun (paperSupportedChangeRingK0_comp σ z φ) y
  exact congrArg (paperRankEulerK0 lam hfg (φ ∘ σ ∘ z) hJ hfin U hU hs) hc

end composition

variable {A R S : Type u} [CommRing A] [CommRing R] [Nontrivial R] [Algebra A R]
  [CommRing S] [Nontrivial S] {G : Type u} [Group G]
  [MulSemiringAction G R] [SMulCommClass G A R]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (a : Fin e → A)
  {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ algebraMap A R ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (φ ∘ algebraMap A R ∘ a))
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

omit [Nontrivial R] [Nontrivial S] in
/-- A 上のひねりを係数写像に合成しても、パラメータの像は変わらない。 -/
lemma paperTwist_comp_parameters (g : G) :
    (φ.comp (MulSemiringAction.toAlgHom A R g).toRingHom) ∘ (algebraMap A R ∘ a) =
      φ ∘ algebraMap A R ∘ a := by
  funext j
  exact congrArg φ ((MulSemiringAction.toAlgHom A R g).commutes (a j))

set_option maxHeartbeats 800000 in
-- 群作用の定義と、支持の指定を保つ係数変更の比較に必要。
/-- 群作用後の正規化 Euler 評価を、ひねった係数写像で計算する。 -/
theorem paperBaseChangeEulerK0_smul (g : G)
    (hJg : J ≤ (Ideal.span (Set.range
      ((φ.comp (MulSemiringAction.toAlgHom A R g).toRingHom) ∘ algebraMap A R ∘ a))).radical)
    (hfing : LengthAlgebra.KoszulFinite lam
      ((φ.comp (MulSemiringAction.toAlgHom A R g).toRingHom) ∘ algebraMap A R ∘ a))
    (y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A R ∘ a)).FullSubcategory) :
    paperBaseChangeEulerK0 φ (algebraMap A R ∘ a) lam hfg hJ hfin U hU hs (g • y) =
    paperBaseChangeEulerK0 (φ.comp (MulSemiringAction.toAlgHom A R g).toRingHom)
      (algebraMap A R ∘ a) lam hfg hJg hfing U hU hs y :=
  paperBaseChangeEulerK0_comp_to (MulSemiringAction.toAlgHom A R g).toRingHom φ
    (algebraMap A R ∘ a) (algebraMap A R ∘ a) (paperTwist_parameters a g)
    lam hfg hJ hfin hJg hfing U hU hs y

set_option maxHeartbeats 800000 in
-- ひねりを合成した写像と元の写像の Koszul 評価の比較に必要。
/-- 各共役の Euler 数にも、同じ振幅・零作用・極小性から共通の下界が成り立つ。 -/
theorem paperBaseChangeEuler_smul_minimal_lower_bound
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (algebraMap A R ∘ a)
      ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, algebraMap A R (a j) ^ v •
      𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ φ (algebraMap A R (a j)) ^ v) i) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal R) (Q : Ideal S) (g : G)
    (hIQ : ∀ r ∈ I, φ (g • r) ∈ Q) (hQ : IsPowTorsion J (S ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, algebraMap A R (a j) ^ v ∈ I) :
    (lam.len (S ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperBaseChangeEulerK0 φ (algebraMap A R ∘ a) lam hfg hJ hfin U hU hs
        (g • TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  let φg := φ.comp (MulSemiringAction.toAlgHom A R g).toRingHom
  have he : φg ∘ algebraMap A R ∘ a = φ ∘ algebraMap A R ∘ a :=
    paperTwist_comp_parameters φ a g
  have hJg : J ≤ (Ideal.span (Set.range (φg ∘ algebraMap A R ∘ a))).radical := by
    rw [he]
    exact hJ
  have hfing : LengthAlgebra.KoszulFinite lam (φg ∘ algebraMap A R ∘ a) := by
    rw [he]
    exact hfin
  rw [paperBaseChangeEulerK0_smul φ a lam hfg hJ hfin U hU hs g hJg hfing]
  apply paperBaseChangeEuler_minimal_lower_bound φg (algebraMap A R ∘ a) lam hfg hJg hfing
    U hU hs K hK h v hv hx ?_ hbound I Q hIQ hQ hmin hzI
  have hepow : (fun j ↦ φg (algebraMap A R (a j)) ^ v) =
      (fun j ↦ φ (algebraMap A R (a j)) ^ v) := by
    funext j
    exact congrArg (fun x ↦ x ^ v) (congrFun he j)
  change ∀ i : ℕ, 0 < i →
    lam.len (koszulHomologySelf (fun j ↦ φg (algebraMap A R (a j)) ^ v) i) = 0
  rw [hepow]
  exact hzero

end SerrePositivity.Asymptotic
