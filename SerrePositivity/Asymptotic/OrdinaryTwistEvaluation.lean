module

public import SerrePositivity.Asymptotic.PaperComplexBaseChange
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength

/-! # 実際の群作用に対する通常長さ評価の不変性

自己同型によるホモロジー長の不変性を公式 (4.2) に適用し、反復錐を消去する。
極小性や近似の Tor 極限を仮定せず、商で支持される任意の複体列について証明する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    (NormalizedLength.ordinary R).len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))

set_option maxHeartbeats 800000 in
-- 二つの支持部分圏のホモロジー評価と係数変更の型の比較に必要。
/-- 通常の各次数の評価は、任意の自己同型による係数拡大で変わらない。 -/
theorem paperOrdinaryBetti_equiv (σ : R ≃+* R) :
    paperBaseChangeBetti σ.toRingHom z (NormalizedLength.ordinary R)
      Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv (RingHom.id R) σ z hfin)
      U hU hs ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ =
    paperRankBetti (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le hfin
      U hU hs ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ := by
  obtain ⟨v, hv, hx⟩ := (show scalarSupported z _ from h)
  apply coneLength_pow_cancel_of_hasFiniteSupport e _ _
    (paperBaseChangeBetti_hasFiniteSupport ..) (paperRankBetti_hasFiniteSupport ..)
  funext q
  have hleft := paperBaseChangeBetti_koszul_tensor_formula σ.toRingHom z
    (NormalizedLength.ordinary R) Submodule.fg_bot bot_le
    (ordinary_koszul_finite_comp_equiv (RingHom.id R) σ z hfin)
    U hU hs K hK h v hv hx (-q)
  have hright := paperRankBetti_koszul_formula (NormalizedLength.ordinary R)
    Submodule.fg_bot z bot_le hfin U hU hs K hK h v hv hx (-q)
  have hn : (fun n ↦ ((NormalizedLength.ordinary R).len
      ((baseChange σ.toRingHom (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex n).obj K))).homology (-(-q)))).toReal) =
      (fun n ↦ ((NormalizedLength.ordinary R).len
        ((koszulComplexOn (fun j ↦ z j ^ v)
          ((evaluateComplex n).obj K)).homology (-(-q)))).toReal) := by
    funext n
    exact congrArg (fun a : ℕ∞ ↦ (a : ℝ≥0∞).toReal)
      (length_homology_baseChange_equiv σ _ _)
  rw [hn] at hleft
  simpa only [coneLength_binomial, neg_sub, sub_neg_eq_add, add_comm] using
    hleft.symm.trans hright

/-- 通常 Euler 評価も自己同型による係数拡大で変わらない。 -/
theorem paperOrdinaryEulerK0_equiv (σ : R ≃+* R) :
    paperBaseChangeEulerK0 σ.toRingHom z (NormalizedLength.ordinary R)
      Submodule.fg_bot bot_le (ordinary_koszul_finite_comp_equiv (RingHom.id R) σ z hfin)
      U hU hs (TriangulatedK0.mk
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) =
    paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le hfin
      U hU hs (TriangulatedK0.mk
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  rw [paperBaseChangeEulerK0_mk, paperRankEulerK0_mk]
  congr 1
  funext q
  congr 1
  exact congrFun (paperOrdinaryBetti_equiv z hfin U hU hs K hK h σ) q

set_option maxHeartbeats 800000 in
-- パラメータの等式による移送と、K₀ 写像の定義の比較に必要。
/-- 支持のパラメータを指定する係数変更についての通常 Euler 不変性。 -/
theorem paperOrdinaryEulerK0_changeRingTo (σ : R ≃+* R) (w : Fin e → R)
    (hw : σ ∘ z = w)
    (hfinw : ∀ v : ℕ, 0 < v → ∀ q,
      (NormalizedLength.ordinary R).len ((koszulComplex (fun j ↦ w j ^ v)).homology q) ≠ ⊤) :
    paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot w bot_le hfinw
      U hU hs (TriangulatedK0.mk ((paperSupportedChangeRingTo σ.toRingHom z w hw).obj
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩)) =
    paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot z bot_le hfin
      U hU hs (TriangulatedK0.mk
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) := by
  subst w
  have he := paperOrdinaryEulerK0_equiv z hfin U hU hs K hK h σ
  rw [paperBaseChangeEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk] at he
  exact he

variable {A : Type u} [CommRing A] [Algebra A R]
  (a : Fin e → A) {G : Type u} [Group G] [MulSemiringAction G R] [SMulCommClass G A R]

/-- 論文の支持つき K₀ 上の実際の群作用に対する通常 Euler 不変性。 -/
theorem paperOrdinaryEulerK0_smul
    (hfinA : ∀ v : ℕ, 0 < v → ∀ q,
      (NormalizedLength.ordinary R).len
        ((koszulComplex (fun j ↦ algebraMap A R (a j) ^ v)).homology q) ≠ ⊤)
    (hA : paperSupportedRank (algebraMap A R ∘ a)
      ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) (g : G) :
    paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot (algebraMap A R ∘ a)
      bot_le hfinA U hU hs (g • TriangulatedK0.mk
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hA⟩) =
    paperRankEulerK0 (NormalizedLength.ordinary R) Submodule.fg_bot (algebraMap A R ∘ a)
      bot_le hfinA U hU hs (TriangulatedK0.mk
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hA⟩) := by
  rw [paperK0_smul_mk]
  exact paperOrdinaryEulerK0_changeRingTo (algebraMap A R ∘ a) hfinA U hU hs K hK hA
    (MulSemiringAction.toRingEquiv G R g) _ (paperTwist_parameters a g) hfinA

end SerrePositivity.Asymptotic
