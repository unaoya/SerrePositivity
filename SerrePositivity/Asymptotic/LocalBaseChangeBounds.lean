module

public import SerrePositivity.Asymptotic.PaperTwistLowerBound
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 局所係数変更後の振幅・極小性と共役の下界

自由複体列の係数変更について、振幅と極小性を元の列から確認する。
局所環の自己同型は極大イデアルを保つので、全共役の下界に必要な
イデアル条件は、ひねる前の一つの条件から従う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter IsLocalRing

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {B T : Type u} [CommRing B] [CommRing T] {s : ℕ → ℕ} (φ : B →+* T)

/-- 自由複体列の各段の振幅は、任意の係数変更で保たれる。 -/
lemma changeRing_evaluate_amplitude
    (K : CochainComplex (FreeSequence B s) ℤ) (a b : ℤ)
    (hb : ∀ n q, q < a ∨ b < q → IsZero (((evaluateComplex n).obj K).X q)) :
    ∀ n q, q < a ∨ b < q → IsZero (((evaluateComplex n).obj
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)).X q) := by
  intro n q hq
  exact ((ModuleCat.extendScalars φ).map_isZero (hb n q hq)).of_iso
    ((HomologicalComplex.eval _ _ q).mapIso (FreeSequence.evaluateComplexTensorIso φ n K)).symm

variable [IsLocalRing B] [IsLocalRing T] [IsLocalHom φ]

/-- 局所準同型による行列の係数変更は、極小性を保つ。 -/
lemma changeRing_minimal
    (K : CochainComplex (FreeSequence B s) ℤ)
    (hmin : ∀ n (x : Fin ((K.X (-1)).rank n) → B) j,
      K.d (-1) 0 n x j ∈ maximalIdeal B) :
    let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
    ∀ n (x : Fin ((L.X (-1)).rank n) → T) j, L.d (-1) 0 n x j ∈ maximalIdeal T := by
  intro L n x j
  exact FreeSequence.changeMatrix_mem_ideal φ (K.d (-1) 0 n)
    (maximalIdeal B) (maximalIdeal T) (fun r hr ↦ map_nonunit φ r hr) (hmin n) x j

section conjugates

variable {A R C : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
  [Algebra A R] [IsLocalHom (algebraMap A R)] [CommRing C] [Nontrivial C]
  {G : Type u} [Group G] [MulSemiringAction G R] [SMulCommClass G A R]
  (ψ : R →+* C) {e : ℕ} (a : Fin e → A)
  {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (ψ ∘ algebraMap A R ∘ a))).radical)
  (hfin : LengthAlgebra.KoszulFinite lam (ψ ∘ algebraMap A R ∘ a))
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 局所環の極大イデアル条件を、群作用つきの支持部分圏の下界へ渡す。
/-- 極小な支持つき複体の全共役の下界。消去指数と共役ごとのイデアル条件を内部で選ぶ。 -/
theorem paperBaseChangeEuler_smul_lower_bound_of_local
    (ha : ∀ j, a j ∈ maximalIdeal A)
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ ψ (algebraMap A R (a j)) ^ v) i) = 0)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank (algebraMap A R ∘ a)
      ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hbound : ∀ n q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex n).obj K).X q))
    (hmin : ∀ n (x : Fin ((K.X (-1)).rank n) → R) j,
      K.d (-1) 0 n x j ∈ maximalIdeal R)
    (Q : Ideal C) (hQmap : ∀ r ∈ maximalIdeal R, ψ r ∈ Q)
    (hQ : IsPowTorsion J (C ⧸ Q)) (g : G) :
    (lam.len (C ⧸ Q)).toReal * normalizedLimit U s (fun n ↦ ((K.X 0).rank n : ℝ)) ≤
      paperBaseChangeEulerK0 ψ (algebraMap A R ∘ a) lam hfg hJ hfin U hU hs
        (g • TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  obtain ⟨v, hv, hx⟩ := (show scalarSupported (algebraMap A R ∘ a) _ from h)
  apply paperBaseChangeEuler_smul_minimal_lower_bound ψ a lam hfg hJ hfin U hU hs
    K hK h v hv hx (hzero v hv) hbound (maximalIdeal R) Q g ?_ hQ hmin ?_
  · intro r hr
    apply hQmap
    rw [← map_ringEquiv_maximalIdeal (MulSemiringAction.toRingEquiv G R g)]
    exact Ideal.mem_map_of_mem _ hr
  · intro j
    exact (maximalIdeal R).pow_mem_of_mem (map_nonunit (algebraMap A R) _ (ha j)) v hv

end conjugates

end SerrePositivity.Asymptotic
