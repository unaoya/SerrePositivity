module

public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation
public import SerrePositivity.Asymptotic.RankVanishing

/-! # 論文の支持圏での係数変更後の消滅

実際のテンソル Koszul 複体で振幅を確認し、計算側との三角同値と共通の
反復錐定理によって論文側の Hᶜ の消滅を得る。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)
  {I : Ideal S} (lam : NormalizedLength S I) (hfg : I.FG)
  (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 二つの係数環と二つの支持部分圏の間の型の比較に必要。
/-- 論文と同じテンソル Koszul の振幅から、係数変更後の対象としての消滅を得る。
元の列の一様支持は要求しない。 -/
theorem paperBaseChangeHomology_vanishing_of_koszul
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q → normalizedLimit U s (fun t ↦ (lam.len
      ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex t).obj K))).homology q)).toReal) = 0)
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((paperBaseChangeHomology φ z lam hfg hI hfin U hU hs q).obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  have hxL := paperBaseChange_complex_smul_zero φ z K hK v hx
  let h' : scalarSupported (φ ∘ z)
      (completedSequenceFunctor.obj (sequenceHomotopyObj L hL)) := ⟨v, hv, hxL⟩
  have hKosL (i : ℤ) (hi : i < a ∨ b < i) : normalizedLimit U s (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ (φ ∘ z) j ^ v)
        ((evaluateComplex t).obj L)).homology i)).toReal) = 0 := by
    have heq : φ ∘ (fun j ↦ z j ^ v) = (fun j ↦ φ (z j) ^ v) := by
      funext j
      simp
    have hfun : (fun t ↦ (lam.len ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
          ((evaluateComplex t).obj K))).homology i)).toReal) =
        (fun t ↦ (lam.len ((koszulComplexOn (fun j ↦ (φ ∘ z) j ^ v)
          ((evaluateComplex t).obj L)).homology i)).toReal) := by
      funext t
      let eq := baseChangeKoszulOnIso φ (fun j ↦ z j ^ v) ((evaluateComplex t).obj K) ≪≫
        eqToIso (congrArg (fun x ↦ koszulComplexOn x
          (baseChange φ ((evaluateComplex t).obj K))) heq) ≪≫
        (koszulFunctor (fun j ↦ φ (z j) ^ v)).mapIso
          (FreeSequence.evaluateComplexTensorIso φ t K)
      exact congrArg ENNReal.toReal (lam.len_congr _ _
        (((HomologicalComplex.homologyFunctor _ _ i).mapIso eq).toLinearEquiv))
    rw [← hfun]
    exact hKos i hi
  have hv' := completedRankHomology_vanishing_of_koszul lam hfg (φ ∘ z) hI hfin U hU hs
    L hL h' v hv hxL a b hKosL q hq
  exact hv'.of_iso ((completedRankHomology lam hfg (φ ∘ z) hI hfin U hU hs q).mapIso
    (paperBaseChangeComplexIso φ z K hK h h'))

set_option maxHeartbeats 800000 in
-- 二つの係数環上で、具体的な評価複体と係数変更を同一視する。
/-- (Kosₘ) を各段の自由振幅と環自身の Koszul 消滅で確認する版。 -/
theorem paperBaseChangeHomology_vanishing
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ φ (z j) ^ v) i) = 0)
    (a b : ℤ)
    (hbound : ∀ t q, q < a ∨ b < q → IsZero (((evaluateComplex t).obj K).X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) :
    IsZero ((paperBaseChangeHomology φ z lam hfg hI hfin U hU hs q).obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  have hxL := paperBaseChange_complex_smul_zero φ z K hK v hx
  let h' : scalarSupported (φ ∘ z)
      (completedSequenceFunctor.obj (sequenceHomotopyObj L hL)) := ⟨v, hv, hxL⟩
  have hb (t : ℕ) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero (((evaluateComplex t).obj L).X i) :=
    ((ModuleCat.extendScalars φ).map_isZero (hbound t i hi)).of_iso
      ((HomologicalComplex.eval _ _ i).mapIso (FreeSequence.evaluateComplexTensorIso φ t K)).symm
  have hz := completedRankHomology_vanishing lam hfg (φ ∘ z) hI hfin U hU hs
    L hL h' v hv hxL hzero a b hb q hq
  exact hz.of_iso ((completedRankHomology lam hfg (φ ∘ z) hI hfin U hU hs q).mapIso
    (paperBaseChangeComplexIso φ z K hK h h'))

/-- 対象としての消滅を、本文の非負実数値の消滅として取り出す。 -/
lemma paperBaseChangeBetti_eq_zero_of_isZero
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ)
    (h : IsZero ((paperBaseChangeHomology φ z lam hfg hI hfin U hU hs q).obj X)) :
    paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q = 0 :=
  (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mpr h

end SerrePositivity.Asymptotic
