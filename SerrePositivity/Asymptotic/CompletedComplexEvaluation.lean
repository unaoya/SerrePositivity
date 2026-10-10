module

public import SerrePositivity.Asymptotic.CompletedKoszulFormula

/-! # 実際の一様支持複体列での完備化後の評価 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

/-- 一様支持複体の直接の像と、支持つき商を経由した像の比較。 -/
noncomputable def completedComplexSupportedIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK))
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    completedComplexObj z K hK h ≅
      (supportedKaroubiFunctor z).obj ((toKaroubi _).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
          ⟨sequenceHomotopyObj K hK, hzK⟩)) := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let L := (B.inverseImage A.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let F := supportedRankQuotientInclusion (s := s) z
  let X : A.FullSubcategory := ⟨sequenceHomotopyObj K hK, hzK⟩
  let i : sequenceRankQuotientFunctor.obj X.obj ≅ F.obj (L.obj X) :=
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).app X
  exact ObjectProperty.isoMk _ ((toKaroubi _).mapIso i ≪≫
    (((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app (L.obj X)).symm)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 一様支持複体列では、完備化後の値は各段のホモロジー長の正規化超極限。 -/
lemma completedRankBetti_complex
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK))
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) q =
      normalizedLimit U s (fun n ↦ (lam.len (((evaluateComplex n).obj K).homology q)).toReal) := by
  rw [completedRankBetti_iso lam hfg z hJ hfin U hU hs
    (completedComplexSupportedIso z K hK hzK h) q,
    completedRankBetti_obj]
  exact supportedRankHomology_length_complex lam hfg z hJ hfin U hU hs K hK hzK q

/-- 公式 (4.2)：商でパラメータの冪が零なら、Koszul ホモロジー長の超極限が
元の非負な係数の二項畳み込みで計算される。元の複体列の一様支持は仮定しない。 -/
theorem completedRankBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex n).obj K)).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        completedRankBetti lam hfg z hJ hfin U hU hs
          (completedComplexObj z K hK h) (-(i - j)) := by
  let x := fun j ↦ z j ^ v
  let h' := sequenceKoszul_map_supported completedSequenceFunctor z x K hK h
  have he := completedRankBetti_sequenceKoszul z lam hfg hJ hfin U hU hs x K hK h hx (-i)
  rw [completedRankBetti_complex z lam hfg hJ hfin U hU hs _ _
    (sequenceKoszul_pow_supported z v hv K hK) h' (-i)] at he
  have hn : (fun n ↦
      (lam.len (((evaluateComplex n).obj (sequenceKoszul x K)).homology (-i))).toReal) =
      (fun n ↦ (lam.len
        ((koszulComplexOn x ((evaluateComplex n).obj K)).homology (-i))).toReal) := by
    funext n
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        (evaluateSequenceKoszulIso x K n)).toLinearEquiv))
  rw [hn] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  omega

end SerrePositivity.Asymptotic
