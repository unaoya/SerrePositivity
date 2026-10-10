module

public import SerrePositivity.Asymptotic.RankMinimalLowerBound
public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation

/-! # 係数変更後の Euler 下界

微分の座標のイデアル条件を係数変更で移し、ランク商の共通下界を論文側へ送る。
元の環が局所環で、その極大イデアルを選べば本文の極小性による下界になる。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

/-- 微分の像の座標がイデアルに入る条件は、任意の環準同型による係数変更で保たれる。 -/
lemma FreeSequence.changeMatrix_mem_ideal
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R))
    (I : Ideal R) (Q : Ideal S) (hIQ : ∀ r ∈ I, φ r ∈ Q)
    (hf : ∀ m j, f m j ∈ I) (m : Fin a → S) (j : Fin b) :
    FreeSequence.changeMatrix φ f m j ∈ Q := by
  classical
  simp only [FreeSequence.changeMatrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.map_apply, LinearMap.toMatrix'_apply]
  exact Q.sum_mem fun k _ ↦ Q.mul_mem_right (m k) (hIQ _ (hf _ j))

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)
  {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二つの係数環と支持つき商の比較を含むため、型の比較に余裕を与える。
/-- 元の複体の極小性と、係数環の Koszul 消滅を別々に確認する Euler 下界。 -/
theorem paperBaseChangeEuler_minimal_lower_bound
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ φ (z j) ^ v) i) = 0)
    (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))
    (I : Ideal R) (Q : Ideal S) (hIQ : ∀ r ∈ I, φ r ∈ Q)
    (hQ : IsPowTorsion J (S ⧸ Q))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I) :
    (lam.len (S ⧸ Q)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
        (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  have hxL := paperBaseChange_complex_smul_zero φ z K hK v hx
  let h' : scalarSupported (φ ∘ z)
      (completedSequenceFunctor.obj (sequenceHomotopyObj L hL)) := ⟨v, hv, hxL⟩
  have hb (t : ℕ) (i : ℤ) (hi : i < -(e : ℤ) ∨ 0 < i) :
      IsZero (((evaluateComplex t).obj L).X i) :=
    ((ModuleCat.extendScalars φ).map_isZero (hbound t i hi)).of_iso
      ((HomologicalComplex.eval _ _ i).mapIso (FreeSequence.evaluateComplexTensorIso φ t K)).symm
  have hminL (t : ℕ) (m : Fin ((L.X (-1)).rank t) → S) (j : Fin ((L.X 0).rank t)) :
      (L.d (-1) 0 t m) j ∈ Q :=
    FreeSequence.changeMatrix_mem_ideal φ (K.d (-1) 0 t) I Q hIQ (hmin t) m j
  have hzQ (j : Fin e) : (φ ∘ z) j ^ v ∈ Q := by
    simpa only [Function.comp_apply, ← map_pow] using hIQ _ (hzI j)
  have hle := completedRankEuler_minimal_lower_bound lam hfg (φ ∘ z) hJ hfin U hU hs
    L hL h' v hv hxL hzero hb Q hQ hminL hzQ
  have hr : (L.X 0).rank = (K.X 0).rank := rfl
  rw [hr] at hle
  simpa only [paperBaseChangeEulerK0, paperRankEulerK0, AddMonoidHom.comp_apply,
    TriangulatedK0.map_mk, completedRankEulerK0_mk,
    completedRankEuler_iso lam hfg (φ ∘ z) hJ hfin U hU hs
      (paperBaseChangeComplexIso φ z K hK h h')] using hle

end SerrePositivity.Asymptotic
