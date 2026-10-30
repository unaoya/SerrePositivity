module

public import SerrePositivity.Asymptotic.PaperRankEvaluation
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 複体列の評価は支持を示すパラメータ系によらない

二つの支持条件を満たす同じ商の対象を、二組の Koszul 複体で一様支持へ移す。
各段のホモロジー長による計算を比較し、共通の零錐の消去定理で元の評価を復元する。
元の複体列の一様支持も、二つの生成イデアルの根基の一致も要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e f : ℕ} (z : Fin e → R) (w : Fin f → R)
  (hJz : J ≤ (Ideal.span (Set.range z)).radical)
  (hJw : J ≤ (Ideal.span (Set.range w)).radical)
  (hfinz : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)
  (hfinw : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ w j ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 一方の支持が商をとる前からある場合、もう一方の Koszul 操作だけで評価を比較できる。 -/
lemma completedRankBetti_independent_of_uniform_support
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hseq : supportedSequence z (sequenceHomotopyObj K hK))
    (hz : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hw : scalarSupported w (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    completedRankBetti lam hfg z hJz hfinz U hU hs (completedComplexObj z K hK hz) =
      completedRankBetti lam hfg w hJw hfinw U hU hs (completedComplexObj w K hK hw) := by
  obtain ⟨v, hv, hx⟩ := (show scalarSupported w _ from hw)
  apply coneLength_pow_cancel_of_hasFiniteSupport f _ _
    (completedRankBetti_hasFiniteSupport ..) (completedRankBetti_hasFiniteSupport ..)
  funext q
  rw [← completedRankBetti_sequenceKoszul_pow z lam hfg hJz hfinz U hU hs
    (fun j ↦ w j ^ v) K hK hz hx q,
    ← completedRankBetti_sequenceKoszul_pow w lam hfg hJw hfinw U hU hs
      (fun j ↦ w j ^ v) K hK hw hx q]
  have hLz := sequenceKoszul_map_supported (𝟭 (SequenceHomotopy R s)) z
    (fun j ↦ w j ^ v) K hK hseq
  have hLw := sequenceKoszul_pow_supported w v hv K hK
  rw [completedRankBetti_complex z lam hfg hJz hfinz U hU hs _ _ hLz,
    completedRankBetti_complex w lam hfg hJw hfinw U hU hs _ _ hLw]

/-- 商でのみ支持をもつ複体列でも、二つの支持の指定による各次数の評価は一致する。 -/
theorem completedRankBetti_complex_support_independent
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hz : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hw : scalarSupported w (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    completedRankBetti lam hfg z hJz hfinz U hU hs (completedComplexObj z K hK hz) =
      completedRankBetti lam hfg w hJw hfinw U hU hs (completedComplexObj w K hK hw) := by
  obtain ⟨v, hv, hx⟩ := (show scalarSupported z _ from hz)
  apply coneLength_pow_cancel_of_hasFiniteSupport e _ _
    (completedRankBetti_hasFiniteSupport ..) (completedRankBetti_hasFiniteSupport ..)
  funext q
  rw [← completedRankBetti_sequenceKoszul_pow z lam hfg hJz hfinz U hU hs
    (fun j ↦ z j ^ v) K hK hz hx q,
    ← completedRankBetti_sequenceKoszul_pow w lam hfg hJw hfinw U hU hs
      (fun j ↦ z j ^ v) K hK hw hx q]
  exact congrFun (completedRankBetti_independent_of_uniform_support lam hfg z w hJz hJw
    hfinz hfinw U hU hs _ _ (sequenceKoszul_pow_supported z v hv K hK) _ _) q

/-- 論文の商においても、同じ複体列の各次数の評価は支持の指定によらない。 -/
theorem paperRankBetti_complex_support_independent
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hz : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hw : paperSupportedRank w ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    paperRankBetti lam hfg z hJz hfinz U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hz⟩ =
    paperRankBetti lam hfg w hJw hfinw U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hw⟩ := by
  funext q
  change completedRankBetti _ _ _ _ _ _ _ _ _ _ = completedRankBetti _ _ _ _ _ _ _ _ _ _
  rw [completedRankBetti_iso lam hfg z hJz hfinz U hU hs (paperComplexComparison z K hK hz),
    completedRankBetti_iso lam hfg w hJw hfinw U hU hs (paperComplexComparison w K hK hw)]
  exact congrFun (completedRankBetti_complex_support_independent lam hfg z w hJz hJw
    hfinz hfinw U hU hs K hK _ _) q

/-- 同じ複体列の Euler 評価も支持の指定によらない。 -/
theorem paperRankEulerK0_complex_support_independent
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (hz : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hw : paperSupportedRank w ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    paperRankEulerK0 lam hfg z hJz hfinz U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hz⟩) =
    paperRankEulerK0 lam hfg w hJw hfinw U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), hw⟩) := by
  simp only [paperRankEulerK0_mk]
  congr 1
  funext q
  congr 1
  exact congrFun (paperRankBetti_complex_support_independent lam hfg z w
    hJz hJw hfinz hfinw U hU hs K hK hz hw) q

end SerrePositivity.Asymptotic
