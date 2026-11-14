module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.Asymptotic.Completed
public import SerrePositivity.CategoryTheory.ScalarSupport
public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.Asymptotic.Euler
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import Mathlib.Algebra.Algebra.Hom
public import SerrePositivity.HomologicalAlgebra.KoszulOrdinaryLength

/-! # 論文の台つき圏の評価・係数変更・ひねり

## 概要

論文の台つき圏の上のホモロジー評価と K₀、根基が同じパラメータ系への台の変更、小さいランクの複体を経由するスカラー作用、小さいランクの尾部を切り捨てる比較、複体の列の評価が台を示すパラメータ系によらないこと、論文の台つき圏の上の係数変更と K₀ の評価、恒等係数変更、台を持つ部分圏と全体の圏での係数変更の比較、公式 (4.2)、具体的な複体の列による係数変更・ひねりと台の変更の後の評価、自己同型によるひねりと K₀ 上の群作用、群作用に対する通常の長さの評価の不変性を与える。

## 方針

Asymptotic のランク商・冪等完備化・Euler 評価を、論文の §4 の言葉に合わせて組み立てる。

## 規約

論文に固有の主張なので Paper/Section4 に置く（refactor-plan §7.2、G の 3）。ひねりは自己同型に沿った係数拡大で、K₀ 上では左作用（有限複体の係数制限による `twist` とは逆元の規約が違う）。

## 使われ方

Paper/Section4 の対称な比較、Paper/Section5。
-/

@[expose] public noncomputable section

universe u v w

section PaperRankEvaluationPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 論文の支持部分圏から長さの Serre 商への第 q 次ホモロジー関手。 -/
noncomputable abbrev paperRankHomology (q : ℤ) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  (paperSupportedRankEquivalence z).functor ⋙ completedRankHomology lam hfg z hJ hfin U hU hs q

instance paperRankHomology_isHomological (q : ℤ) :
    (paperRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by infer_instance

/-- 論文の支持対象の非負なホモロジー長。 -/
noncomputable abbrev paperRankBetti
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  completedRankBetti lam hfg z hJ hfin U hU hs ((paperSupportedRankEquivalence z).functor.obj X) q

lemma paperRankBetti_nonneg (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ paperRankBetti lam hfg z hJ hfin U hU hs X q := completedRankBetti_nonneg ..

lemma paperRankBetti_hasFiniteSupport (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (paperRankBetti lam hfg z hJ hfin U hU hs X) :=
  completedRankBetti_hasFiniteSupport ..

/-- 論文の圏の K₀ 上に定義された Euler 評価。 -/
noncomputable def paperRankEulerK0 :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+ ℝ :=
  (completedRankEulerK0 lam hfg z hJ hfin U hU hs).comp
    (TriangulatedK0.map (paperSupportedRankEquivalence z).functor)

lemma paperRankEulerK0_mk (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    paperRankEulerK0 lam hfg z hJ hfin U hU hs (TriangulatedK0.mk X) =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * paperRankBetti lam hfg z hJ hfin U hU hs X q := by
  rw [paperRankEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedRankEulerK0_mk]
  rfl

/-- 同じ複体列の論文側と計算側の像を、支持部分圏の中で比較する。 -/
noncomputable def paperComplexComparison
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    (paperSupportedRankEquivalence z).functor.obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ ≅
        completedComplexObj z K hK
          ((scalarSupported z).prop_of_iso ((paperSequenceComparison R s).app _)
            (scalarSupported_map z (paperRankEquivalence R s).functor _ h)) :=
  ObjectProperty.isoMk _ ((paperSequenceComparison R s).app _)

set_option maxHeartbeats 800000 in
-- 支持部分圏と圏同値を含む型の比較に必要。
/-- 論文と同じ圏で述べた公式 (4.2) の係数等式。 -/
theorem paperRankBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex n).obj K)).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperRankBetti lam hfg z hJ hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  let E := paperRankEquivalence R s
  let iK := (paperSequenceComparison R s).app (sequenceHomotopyObj K hK)
  have hx' : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0 := by
    intro j
    have he : z j ^ v • 𝟙 (E.functor.obj ((paperSequenceFunctor R s).obj
        (sequenceHomotopyObj K hK))) = 0 := by
      simpa only [Functor.map_smul, E.functor.map_id, E.functor.map_zero] using
        E.functor.congr_map (hx j)
    apply (cancel_epi iK.hom).mp
    simp only [comp_zero, Linear.comp_smul, Category.comp_id] at he ⊢
    simpa using he =≫ iK.hom
  let h' : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) :=
    (scalarSupported z).prop_of_iso iK (scalarSupported_map z E.functor _ h)
  refine (completedRankBetti_koszul_formula z lam hfg hJ hfin U hU hs K hK h' v hv hx' i).trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact (completedRankBetti_iso lam hfg z hJ hfin U hU hs
    (paperComplexComparison z K hK h) _).symm

end SerrePositivity.Asymptotic

end PaperRankEvaluationPart

section PaperSupportChangePart

namespace SerrePositivity.Asymptotic

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e f : ℕ} (z : Fin e → R) (w : Fin f → R)

/-- ランク商での支持を、生成イデアルの根基の包含に沿って変更する。 -/
lemma paperSupportedRank_of_span_le_radical
    (h : Ideal.span (Set.range w) ≤ (Ideal.span (Set.range z)).radical)
    {X : PaperRankQuotient R s} (hX : paperSupportedRank z X) : paperSupportedRank w X :=
  scalarSupported_of_span_le_radical z w h hX

/-- 根基が等しければ、論文の支持圏はパラメータ系によらない。 -/
lemma paperSupportedRank_eq_of_radical_eq
    (h : (Ideal.span (Set.range z)).radical = (Ideal.span (Set.range w)).radical) :
    paperSupportedRank (s := s) z = paperSupportedRank w :=
  scalarSupported_eq_of_radical_eq z w h

end SerrePositivity.Asymptotic

end PaperSupportChangePart

section FactorizationSupportPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

omit [Nontrivial R] in
/-- 段ごとの因子分解を自由列のホモトピーに組み戻す。 -/
lemma assemble_scalar_factorization
    (K G : CochainComplex (FreeSequence R s) ℤ) (r : R)
    (h : ∀ n, ∃ (u : (evaluateComplex n).obj K ⟶ (evaluateComplex n).obj G)
      (v : (evaluateComplex n).obj G ⟶ (evaluateComplex n).obj K),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v))) :
    ∃ (u : K ⟶ G) (v : G ⟶ K), Nonempty (Homotopy (r • 𝟙 K) (u ≫ v)) := by
  choose u v h using h
  refine ⟨assembleChainMap u, assembleChainMap v, (nonempty_homotopy_iff _ _).2 ?_⟩
  intro n
  have : (evaluateComplex (R := R) (s := s) n).Linear R := by
    change ((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Linear R
    infer_instance
  simpa only [Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_comp, evaluate_assembleChainMap] using h n

omit [Nontrivial R] in
/-- 経由する複体の像が零なら、ホモトピックなスカラー作用の像も零。 -/
lemma scalar_zero_of_factorization
    {D : Type w} [Category.{v} D] [Preadditive D] [Linear R D]
    (T : SequenceHomotopy R s ⥤ D) [T.Linear R] [T.Additive]
    (K G : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hG : strictlyBoundedComplex (FreeSequence R s) G)
    (hz : IsZero (T.obj (sequenceHomotopyObj G hG)))
    (r : R) (u : K ⟶ G) (v : G ⟶ K) (h : Homotopy (r • 𝟙 K) (u ≫ v)) :
    r • 𝟙 (T.obj (sequenceHomotopyObj K hK)) = 0 := by
  let u' : sequenceHomotopyObj K hK ⟶ sequenceHomotopyObj G hG :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map u)
  let v' : sequenceHomotopyObj G hG ⟶ sequenceHomotopyObj K hK :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map v)
  have he : r • 𝟙 (sequenceHomotopyObj K hK) = u' ≫ v' := by
    apply ObjectProperty.hom_ext
    change r • 𝟙 _ = (HomotopyCategory.quotient _ _).map u ≫
      (HomotopyCategory.quotient _ _).map v
    have ht := HomotopyCategory.eq_of_homotopy _ _ h
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_comp] at ht
    exact ht
  calc
    _ = T.map (r • 𝟙 (sequenceHomotopyObj K hK)) := by simp
    _ = T.map u' ≫ T.map v' := by rw [he, T.map_comp]
    _ = 0 := by rw [hz.eq_zero_of_tgt (T.map u'), zero_comp]

/-- 小さいランクの複体を経由する作用は、論文の商・完備化の順序でも零になる。 -/
lemma paper_scalar_zero_of_small_factorization
    (K G : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K) (hG : rankSmallComplex G)
    (r : R) (u : K ⟶ G) (v : G ⟶ K) (h : Homotopy (r • 𝟙 K) (u ≫ v)) :
    r • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0 := by
  apply scalar_zero_of_factorization (paperSequenceFunctor R s) K G hK hG.1 _ r u v h
  apply karoubiFirstFromOriginal_kills
  exact ⟨(HomotopyCategory.quotient _ _).obj G,
    (rankSmallHomotopy_quotient G).2 hG, ⟨Iso.refl _⟩⟩

end SerrePositivity.Asymptotic

end FactorizationSupportPart

section TruncationComparisonPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits Asymptotics Filter StupidTruncation

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

/-- 切り捨てる範囲の各項が小さいなら、尾部全体が小さいランクの有界複体である。 -/
lemma below_rankSmall (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    rankSmallComplex (below K (a - 1)) := by
  refine ⟨below_bounded K hK (a - 1), fun q ↦ ?_⟩
  by_cases hq : q ≤ a - 1
  · simpa only [FreeSequence.rank_eq_of_iso (belowXIso K (a - 1) q hq)] using
      hsmall q (by omega)
  · simp only [FreeSequence.rank_eq_zero_of_isZero _
      (below_isZero_X K (a - 1) q (by omega)), Nat.cast_zero]
    exact isLittleO_zero _ _

/-- 小さいランクの尾部を切る包含は、論文のランク商で同型になる。 -/
lemma paper_inclusion_isIso (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    IsIso ((paperSequenceFunctor R s).map (boundedInclusion K hK a)) := by
  apply isIso_map_boundedInclusion (paperSequenceFunctor R s) K hK a
  apply karoubiFirstFromOriginal_kills
  exact ⟨(HomotopyCategory.quotient _ _).obj (below K (a - 1)),
    (rankSmallHomotopy_quotient _).mpr (below_rankSmall K hK a hsmall), ⟨Iso.refl _⟩⟩

/-- 切り詰めを変えても、ランク商の対象は同型である。 -/
noncomputable def paperTruncationIso (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    (paperSequenceFunctor R s).obj (sequenceHomotopyObj (above K a) (above_bounded K hK a)) ≅
      (paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK) := by
  have := paper_inclusion_isIso K hK a hsmall
  exact asIso ((paperSequenceFunctor R s).map (boundedInclusion K hK a))

/-- 支持つき K₀ の類も変わらず、任意の Euler 評価に使える。 -/
lemma paperTruncation_K0_eq {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) (a : ℤ)
    (hsmall : ∀ q < a, (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)))
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    TriangulatedK0.mk
      (⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj (above K a) (above_bounded K hK a)),
        (scalarSupported z).prop_of_iso (paperTruncationIso K hK a hsmall).symm h⟩ :
        (paperSupportedRank (s := s) z).FullSubcategory) =
      TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ := by
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (paperTruncationIso K hK a hsmall))

end SerrePositivity.Asymptotic

end TruncationComparisonPart

section ComplexEvaluationIndependencePart

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

end ComplexEvaluationIndependencePart

section PaperBaseChangePart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 支持圏の三角同値に沿って、論文の圏上に移した係数変更。 -/
noncomputable abbrev paperSupportedChangeRing :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤
      (paperSupportedRank (s := s) (φ ∘ z)).FullSubcategory :=
  (paperSupportedToKaroubi z).functor ⋙
    (functorExtension₂ _ _).obj (supportedRankChangeRing φ z) ⋙
      (paperSupportedToKaroubi (φ ∘ z)).inverse

/-- 係数変更の前後で、支持つき商を用いた計算モデルとの比較が可換。 -/
noncomputable def paperSupportedChangeRingFactors :
    paperSupportedChangeRing (s := s) φ z ⋙ (paperSupportedToKaroubi (φ ∘ z)).functor ≅
      (paperSupportedToKaroubi z).functor ⋙
        (functorExtension₂ _ _).obj (supportedRankChangeRing φ z) :=
  isoWhiskerLeft ((paperSupportedToKaroubi z).functor ⋙
    (functorExtension₂ _ _).obj (supportedRankChangeRing φ z))
    (paperSupportedToKaroubi (φ ∘ z)).counitIso

/-- 論文の支持圏でも二段階の係数変更と直接の係数変更が一致する。 -/
noncomputable def paperSupportedChangeRingCompIso
    {T : Type u} [CommRing T] [Nontrivial T] (ψ : S →+* T) :
    paperSupportedChangeRing (s := s) φ z ⋙ paperSupportedChangeRing ψ (φ ∘ z) ≅
      paperSupportedChangeRing (ψ.comp φ) z :=
  isoWhiskerRight (paperSupportedChangeRingFactors φ z)
    ((functorExtension₂ _ _).obj (supportedRankChangeRing ψ (φ ∘ z)) ⋙
      (paperSupportedToKaroubi (ψ ∘ φ ∘ z)).inverse) ≪≫
    isoWhiskerLeft (paperSupportedToKaroubi z).functor
      (isoWhiskerRight (completedSupportedChangeRingCompIso φ ψ z)
        (paperSupportedToKaroubi ((ψ.comp φ) ∘ z)).inverse)

/-- 二段階の係数変更は K₀ 上でも直接の係数変更と同じ写像を与える。 -/
lemma paperSupportedChangeRingK0_comp
    {T : Type u} [CommRing T] [Nontrivial T] (ψ : S →+* T) :
    (TriangulatedK0.map (paperSupportedChangeRing (s := s) ψ (φ ∘ z))).comp
      (TriangulatedK0.map (paperSupportedChangeRing (s := s) φ z)) =
        TriangulatedK0.map (paperSupportedChangeRing (s := s) (ψ.comp φ) z) := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk]
  exact TriangulatedK0.mk_iso ((paperSupportedChangeRingCompIso φ z ψ).app X)

variable {J : Ideal R} {I : Ideal S} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 論文の圏の Euler 評価を計算モデルへ移す。 -/
lemma paperRankEulerK0_viaSupported :
    paperRankEulerK0 lam hfg z hJ hfin U hU hs =
      (completedSupportedEulerK0 lam hfg z hJ hfin U hU hs).comp
        (TriangulatedK0.map (paperSupportedToKaroubi z).functor) := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [paperRankEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    completedRankEulerK0_mk, completedSupportedEulerK0_mk]
  rfl

set_option maxHeartbeats 800000 in
-- 支持部分圏、局所化、Karoubi 延長の合成に現れる型の比較に必要。
/-- 論文の圏の K₀ 上の階数倍公式。有限版の比較と A 側の冪等完備性から従う。 -/
theorem paperRankEulerK0_changeRing
    [IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z)]
    (mu : NormalizedLength S I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
    (hfinS : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ (φ (z j)) ^ v)).homology q) ≠ ⊤)
    (c : ℝ)
    (hc : ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ), IsPerfectSupported z P →
      lambdaEuler mu (baseChange φ P) = c * lambdaEuler lam P) :
    (paperRankEulerK0 mu hIfg (φ ∘ z) hI hfinS U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing φ z)) =
        c • paperRankEulerK0 lam hfg z hJ hfin U hU hs := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk, AddMonoidHom.smul_apply,
    smul_eq_mul]
  rw [paperRankEulerK0_viaSupported, paperRankEulerK0_viaSupported]
  simp only [AddMonoidHom.comp_apply, TriangulatedK0.map_mk]
  simp only [completedSupportedEulerK0_mk]
  exact (completedSupportedEuler_iso mu hIfg (φ ∘ z) hI hfinS U hU hs
    ((paperSupportedChangeRingFactors φ z).app X)).trans
      (completedSupportedEuler_changeRing lam hfg z hJ hfin φ mu hIfg hI hfinS U hU hs c hc
        ((paperSupportedToKaroubi z).functor.obj X))

end SerrePositivity.Asymptotic

end PaperBaseChangePart

section BaseChangeIdentityPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 恒等環準同型による自由列の係数変更。 -/
noncomputable def FreeSequence.changeRingIdIso :
    changeRing (s := s) (RingHom.id R) ≅ 𝟭 (FreeSequence R s) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    funext n
    simp [changeRing, changeMatrix])

/-- 恒等加法関手がホモトピー圏に誘導する関手。 -/
noncomputable def freeSequenceHomotopyIdIso :
    (𝟭 (FreeSequence R s)).mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (FreeSequence R s) (.up ℤ)) :=
  Quotient.natIsoLift _ (isoWhiskerRight
    (Functor.mapHomologicalComplexIdIso (FreeSequence R s) (.up ℤ))
    (HomotopyCategory.quotient _ _))

/-- 共通有界ホモトピー圏の恒等係数変更。 -/
noncomputable def sequenceChangeRingIdIso :
    mapBoundedHomotopy (FreeSequence.changeRing (s := s) (RingHom.id R)) ≅
      𝟭 (SequenceHomotopy R s) :=
  ((boundedHomotopyProperty (FreeSequence R s)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (boundedHomotopyInclusion _)
      ((NatIso.mapHomotopyCategory FreeSequence.changeRingIdIso (.up ℤ)) ≪≫
        freeSequenceHomotopyIdIso))

variable {e : ℕ} (z : Fin e → R)

/-- 支持部分圏の恒等係数変更。 -/
noncomputable def supportedSequenceChangeRingIdIso :
    supportedSequenceChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (supportedSequence (s := s) z).FullSubcategory :=
  ((supportedSequence (s := s) z).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (supportedSequence z).ι sequenceChangeRingIdIso)

variable [Nontrivial R]

/-- 支持つき Verdier 商の恒等係数変更。 -/
noncomputable def supportedRankChangeRingIdIso :
    supportedRankChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (SupportedSequenceRankQuotient (s := s) z) := by
  let Q := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  exact (Localization.fullyFaithfulWhiskeringLeft Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW _).preimageIso
      (supportedRankChangeRingFactors (RingHom.id R) z ≪≫
        isoWhiskerRight (supportedSequenceChangeRingIdIso z) Q)

/-- 冪等完備化した支持つき商の恒等係数変更。 -/
noncomputable def completedSupportedChangeRingIdIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) (RingHom.id R) z) ≅
      𝟭 (Karoubi (SupportedSequenceRankQuotient (s := s) z)) := by
  exact ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app _ ≪≫
      isoWhiskerRight (supportedRankChangeRingIdIso z) (toKaroubi _))

/-- 論文の支持圏の恒等係数変更。 -/
noncomputable def paperSupportedChangeRingIdIso :
    paperSupportedChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (paperSupportedRank (s := s) z).FullSubcategory :=
  isoWhiskerLeft (paperSupportedToKaroubi z).functor
    (isoWhiskerRight (completedSupportedChangeRingIdIso z)
      (paperSupportedToKaroubi z).inverse) ≪≫
    (paperSupportedToKaroubi z).unitIso.symm

/-- 恒等係数変更が K₀ に誘導する写像は恒等写像。 -/
lemma paperSupportedChangeRingK0_id :
    TriangulatedK0.map (paperSupportedChangeRing (s := s) (RingHom.id R) z) =
      AddMonoidHom.id _ := by
  apply TriangulatedK0.hom_ext
  intro X
  exact TriangulatedK0.mk_iso ((paperSupportedChangeRingIdIso z).app X)

end SerrePositivity.Asymptotic

end BaseChangeIdentityPart

section BaseChangeComparisonPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 支持を忘れる関手と商の係数変更の可換性。 -/
noncomputable def supportedRankChangeRingInclusionIso :
    supportedRankChangeRing (s := s) φ z ⋙ supportedRankQuotientInclusion (φ ∘ z) ≅
      supportedRankQuotientInclusion z ⋙ rankQuotientChangeRing φ := by
  let A := supportedSequence (s := s) z
  let A' := supportedSequence (s := s) (φ ∘ z)
  let B := rankSmallBounded (R := R) (s := s)
  let B' := rankSmallBounded (R := S) (s := s)
  let Q := (B.inverseImage A.ι).trW.Q
  let Q' := (B'.inverseImage A'.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let Ψ := A'.triangulatedLocalizerMorphism B'
  let i := CatCommSq.iso Φ.functor Q B.trW.Q (Φ.localizedFunctor Q B.trW.Q)
  let j := CatCommSq.iso Ψ.functor Q' B'.trW.Q (Ψ.localizedFunctor Q' B'.trW.Q)
  exact (Localization.fullyFaithfulWhiskeringLeft Q (B.inverseImage A.ι).trW _).preimageIso
    (isoWhiskerRight (supportedRankChangeRingFactors φ z) (supportedRankQuotientInclusion _) ≪≫
      isoWhiskerLeft (supportedSequenceChangeRing φ z) j.symm ≪≫
      isoWhiskerLeft A.ι (rankQuotientChangeRing_fac φ).symm ≪≫
      isoWhiskerRight i (rankQuotientChangeRing φ))

/-- 全体の完備化上の係数変更を支持部分圏に制限する。 -/
@[implicit_reducible] noncomputable def completedSupportedChangeRing :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory ⥤
      (supportedCompletedRankQuotient (s := s) (φ ∘ z)).FullSubcategory :=
  (supportedCompletedRankQuotient (φ ∘ z)).lift
    ((supportedCompletedRankQuotient z).ι ⋙ completedChangeRing φ)
    (fun X ↦ completedChangeRing_supported φ z X.obj X.property)

noncomputable instance : (completedSupportedChangeRing (s := s) φ z).CommShift ℤ := by
  dsimp only [completedSupportedChangeRing]
  infer_instance

instance : (completedSupportedChangeRing (s := s) φ z).IsTriangulated := by
  dsimp only [completedSupportedChangeRing]
  infer_instance

/-- 支持つき商の完備化と全体の商の完備化での係数変更が一致する。 -/
noncomputable def supportedKaroubiChangeRingIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) φ z) ⋙
      (supportedKaroubiEquivalence (φ ∘ z)).functor ≅
    (supportedKaroubiEquivalence z).functor ⋙ completedSupportedChangeRing φ z := by
  let F := supportedRankChangeRing (s := s) φ z
  let I := supportedRankQuotientInclusion (s := s) z
  let J := supportedRankQuotientInclusion (s := s) (φ ∘ z)
  let G := rankQuotientChangeRing (s := s) φ
  let F' := (functorExtension₂ _ _).obj F
  let I' := (functorExtension₂ _ _).obj I
  let J' := (functorExtension₂ _ _).obj J
  let G' := (functorExtension₂ _ _).obj G
  let a : toKaroubi _ ⋙ F' ⋙ J' ≅ toKaroubi _ ⋙ I' ⋙ G' :=
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F) J' ≪≫
    isoWhiskerLeft F ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app J) ≪≫
    isoWhiskerRight (supportedRankChangeRingInclusionIso φ z) (toKaroubi _) ≪≫
    isoWhiskerLeft I ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G).symm ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app I).symm G'
  let b : F' ⋙ J' ≅ I' ⋙ G' :=
    ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso a
  exact ((supportedCompletedRankQuotient (s := s) (φ ∘ z)).fullyFaithfulι.whiskeringRight
    (Karoubi (SupportedSequenceRankQuotient (s := s) z))).preimageIso b

/-- 論文の圏の係数変更も、全体の圏の係数変更を制限したものと一致する。 -/
noncomputable def paperChangeRingToCompletedIso :
    paperSupportedChangeRing (s := s) φ z ⋙ (paperSupportedRankEquivalence (φ ∘ z)).functor ≅
      (paperSupportedRankEquivalence z).functor ⋙ completedSupportedChangeRing φ z :=
  isoWhiskerLeft (paperSupportedChangeRing φ z ⋙
    (paperSupportedRankEquivalence (φ ∘ z)).functor)
    (supportedKaroubiEquivalence (φ ∘ z)).counitIso.symm ≪≫
  isoWhiskerRight (paperSupportedChangeRingFactors φ z)
    (supportedKaroubiEquivalence (φ ∘ z)).functor ≪≫
  isoWhiskerLeft (paperSupportedToKaroubi z).functor (supportedKaroubiChangeRingIso φ z) ≪≫
  isoWhiskerRight (isoWhiskerLeft (paperSupportedRankEquivalence z).functor
    (supportedKaroubiEquivalence z).counitIso) (completedSupportedChangeRing φ z)

end SerrePositivity.Asymptotic

end BaseChangeComparisonPart

section PaperBaseChangeEvaluationPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents Filter

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 商でパラメータの冪が零なら、係数変更した実際の複体列の像でも零。 -/
lemma paperBaseChange_complex_smul_zero
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (v : ℕ)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0) :
    ∀ j, (φ (z j)) ^ v • 𝟙 (completedSequenceFunctor.obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK))) = 0 := by
  intro j
  let E := (paperRankEquivalence R s).functor
  let F := completedChangeRing (s := s) φ
  have h0 : z j ^ v • 𝟙 (E.obj ((paperSequenceFunctor R s).obj
      (sequenceHomotopyObj K hK))) = 0 := by
    simpa only [E.map_smul, E.map_id, E.map_zero] using E.congr_map (hx j)
  have h1 := smul_id_zero_of_iso ((paperSequenceComparison R s).app
    (sequenceHomotopyObj K hK)) (z j ^ v) h0
  have h2 := F.congr_map h1
  rw [completedChangeRing_map_smul_id, map_pow, F.map_zero] at h2
  exact smul_id_zero_of_iso ((completedChangeRingFactors φ).app
    (sequenceHomotopyObj K hK)) (φ (z j) ^ v) h2

/-- 実際の複体列において、論文側の係数変更と行列の係数変更が一致する。 -/
noncomputable def paperBaseChangeComplexIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hL : scalarSupported (φ ∘ z) (completedSequenceFunctor.obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    (paperSupportedRankEquivalence (φ ∘ z)).functor.obj
      ((paperSupportedChangeRing φ z).obj
        ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) ≅
    completedComplexObj (φ ∘ z)
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
      (changeRing_strictlyBounded φ K hK) hL :=
  (paperChangeRingToCompletedIso φ z).app _ ≪≫
    ObjectProperty.isoMk _ ((completedChangeRing φ).mapIso
      ((paperSequenceComparison R s).app (sequenceHomotopyObj K hK)) ≪≫
        (completedChangeRingFactors φ).app (sequenceHomotopyObj K hK))

variable {I : Ideal S} (lam : NormalizedLength S I) (hfg : I.FG)
  (hI : I ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- T → C の後のホモロジーを測る命題4.3の Hᶜ。 -/
noncomputable abbrev paperBaseChangeHomology (q : ℤ) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  paperSupportedChangeRing φ z ⋙ paperRankHomology lam hfg (φ ∘ z) hI hfin U hU hs q

instance paperBaseChangeHomology_isHomological (q : ℤ) :
    (paperBaseChangeHomology φ z lam hfg hI hfin U hU hs q).IsHomological := by infer_instance

noncomputable abbrev paperBaseChangeBetti
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) : ℝ :=
  paperRankBetti lam hfg (φ ∘ z) hI hfin U hU hs ((paperSupportedChangeRing φ z).obj X) q

lemma paperBaseChangeBetti_nonneg
    (X : (paperSupportedRank (s := s) z).FullSubcategory) (q : ℤ) :
    0 ≤ paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q := paperRankBetti_nonneg ..

lemma paperBaseChangeBetti_hasFiniteSupport
    (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    Function.HasFiniteSupport (paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X) :=
  paperRankBetti_hasFiniteSupport ..

/-- 支持つきランク商での同型は、係数変更後の各次数の評価を保つ。 -/
lemma paperBaseChangeBetti_iso
    {X Y : (paperSupportedRank (s := s) z).FullSubcategory} (i : X ≅ Y) (q : ℤ) :
    paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q =
      paperBaseChangeBetti φ z lam hfg hI hfin U hU hs Y q :=
  completedRankBetti_iso lam hfg (φ ∘ z) hI hfin U hU hs
    ((paperSupportedRankEquivalence (φ ∘ z)).functor.mapIso
      ((paperSupportedChangeRing φ z).mapIso i)) q

noncomputable def paperBaseChangeEulerK0 :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+ ℝ :=
  (paperRankEulerK0 lam hfg (φ ∘ z) hI hfin U hU hs).comp
    (TriangulatedK0.map (paperSupportedChangeRing φ z))

lemma paperBaseChangeEulerK0_mk (X : (paperSupportedRank (s := s) z).FullSubcategory) :
    paperBaseChangeEulerK0 φ z lam hfg hI hfin U hU hs (TriangulatedK0.mk X) =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs X q := by
  rw [paperBaseChangeEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    paperRankEulerK0_mk]

set_option maxHeartbeats 800000 in
-- 二つの係数環にわたる支持部分圏と局所化の型の比較に必要。
/-- 正規化評価版の公式 (4.2)。元の列の一様支持は仮定しない。 -/
theorem paperBaseChangeBetti_koszul_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  have hxL := paperBaseChange_complex_smul_zero φ z K hK v hx
  let h' : scalarSupported (φ ∘ z) (completedSequenceFunctor.obj (sequenceHomotopyObj L hL)) :=
    ⟨v, hv, hxL⟩
  have he := completedRankBetti_koszul_formula (φ ∘ z) lam hfg hI hfin U hU hs
    L hL h' v hv hxL i
  have hn : (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ (φ ∘ z) j ^ v)
        ((evaluateComplex n).obj L)).homology (-i))).toReal) := by
    funext n
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        ((koszulFunctor (fun j ↦ φ (z j) ^ v)).mapIso
          (FreeSequence.evaluateComplexTensorIso φ n K))).toLinearEquiv))
  rw [hn]
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact (completedRankBetti_iso lam hfg (φ ∘ z) hI hfin U hU hs
    (paperBaseChangeComplexIso φ z K hK h h') _).symm

/-- 元の Koszul 複体をさらに S にテンソルする、論文と同じ右辺での公式 (4.2)。 -/
theorem paperBaseChangeBetti_koszul_tensor_formula
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v)
    (hx : ∀ j, z j ^ v • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0)
    (i : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len
      ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        paperBaseChangeBetti φ z lam hfg hI hfin U hU hs
          ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i - j)) := by
  have hn : (fun n ↦ (lam.len ((baseChange φ (koszulComplexOn (fun j ↦ z j ^ v)
        ((evaluateComplex n).obj K))).homology (-i))).toReal) =
      (fun n ↦ (lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
        (baseChange φ ((evaluateComplex n).obj K))).homology (-i))).toReal) := by
    funext n
    have hx' : φ ∘ (fun j ↦ z j ^ v) = (fun j ↦ φ (z j) ^ v) := by ext j; simp
    exact congrArg ENNReal.toReal (lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        (baseChangeKoszulOnIso φ (fun j ↦ z j ^ v) ((evaluateComplex n).obj K) ≪≫
          eqToIso (congrArg (fun x ↦ koszulComplexOn x
            (baseChange φ ((evaluateComplex n).obj K))) hx'))).toLinearEquiv))
  rw [hn]
  exact paperBaseChangeBetti_koszul_formula φ z lam hfg hI hfin U hU hs K hK h v hv hx i

end SerrePositivity.Asymptotic

end PaperBaseChangeEvaluationPart

section PaperTwistPart

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S V : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  [CommRing V] [Nontrivial V] {s : ℕ → ℕ} {e : ℕ}

/-- 係数変更先のパラメータを指定した、論文の支持圏の係数変更。 -/
noncomputable def paperSupportedChangeRingTo (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedRank (s := s) z).FullSubcategory ⥤
      (paperSupportedRank (s := s) w).FullSubcategory := by
  subst w
  exact paperSupportedChangeRing φ z

noncomputable instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedChangeRingTo (s := s) φ z w h).CommShift ℤ := by
  subst w
  dsimp [paperSupportedChangeRingTo]
  infer_instance

instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (paperSupportedChangeRingTo (s := s) φ z w h).IsTriangulated := by
  subst w
  dsimp [paperSupportedChangeRingTo]
  infer_instance

/-- パラメータを指定した係数変更の K₀ 写像。 -/
noncomputable def paperSupportedMap (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory →+
      TriangulatedK0 (paperSupportedRank (s := s) w).FullSubcategory :=
  TriangulatedK0.map (paperSupportedChangeRingTo φ z w h)

/-- 同じ環準同型による写像は、パラメータの等式の証明によらず一致する。 -/
lemma paperSupportedMap_congr (φ ψ : R →+* S) (z : Fin e → R) (w : Fin e → S)
    (h : φ ∘ z = w) (k : ψ ∘ z = w) (hφ : φ = ψ) :
    paperSupportedMap (s := s) φ z w h = paperSupportedMap ψ z w k := by
  subst ψ
  rfl

/-- 指定したパラメータに関しても係数変更の合成則が成り立つ。 -/
lemma paperSupportedMap_comp (φ : R →+* S) (ψ : S →+* V)
    (z : Fin e → R) (w : Fin e → S) (v : Fin e → V)
    (h : φ ∘ z = w) (k : ψ ∘ w = v) :
    (paperSupportedMap (s := s) ψ w v k).comp (paperSupportedMap φ z w h) =
      paperSupportedMap (ψ.comp φ) z v (by rw [← k, ← h]; rfl) := by
  subst w v
  exact paperSupportedChangeRingK0_comp φ z ψ

/-- 恒等写像は支持つき K₀ の恒等写像を誘導する。 -/
lemma paperSupportedMap_id (z : Fin e → R) :
    paperSupportedMap (s := s) (RingHom.id R) z z rfl = AddMonoidHom.id _ :=
  paperSupportedChangeRingK0_id z

variable {A T : Type u} [CommRing A] [CommRing T] [Nontrivial T] [Algebra A T]
  (z : Fin e → A) {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

omit [Nontrivial T] in
/-- A 上の作用は A のパラメータの像を固定する。 -/
lemma paperTwist_parameters (g : G) :
    (MulSemiringAction.toAlgHom A T g).toRingHom ∘ (algebraMap A T ∘ z) =
      algebraMap A T ∘ z :=
  funext fun j ↦ (MulSemiringAction.toAlgHom A T g).commutes (z j)

/-- 自己同型に沿った係数拡大による、論文の支持圏のひねり。 -/
noncomputable abbrev paperTwist (g : G) :
    (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory ⥤
      (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory :=
  paperSupportedChangeRingTo (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (paperTwist_parameters z g)

/-- ひねりが K₀ に誘導する準同型。 -/
noncomputable abbrev paperTwistK0 (g : G) :
    TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory →+
      TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory :=
  TriangulatedK0.map (paperTwist (T := T) z g)

/-- 単位元によるひねりは K₀ 上で恒等写像。 -/
lemma paperTwistK0_one :
    paperTwistK0 (s := s) (T := T) z (1 : G) = AddMonoidHom.id _ := by
  have h : (MulSemiringAction.toAlgHom A T (1 : G)).toRingHom = RingHom.id T :=
    RingHom.ext (one_smul G)
  change paperSupportedMap _ _ _ _ = _
  simp only [h]
  exact paperSupportedMap_id _

/-- 係数拡大によるひねりは K₀ 上で左作用の合成則を満たす。 -/
lemma paperTwistK0_mul (g h : G) :
    paperTwistK0 (s := s) (T := T) z (g * h) =
      (paperTwistK0 (s := s) (T := T) z g).comp (paperTwistK0 (s := s) (T := T) z h) := by
  have hh : (MulSemiringAction.toAlgHom A T (g * h)).toRingHom =
      (MulSemiringAction.toAlgHom A T g).toRingHom.comp
        (MulSemiringAction.toAlgHom A T h).toRingHom :=
    RingHom.ext (mul_smul g h)
  have hc := paperSupportedMap_comp (s := s)
    (MulSemiringAction.toAlgHom A T h).toRingHom
    (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (algebraMap A T ∘ z)
    (paperTwist_parameters z h) (paperTwist_parameters z g)
  change paperSupportedMap (MulSemiringAction.toAlgHom A T (g * h)).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) _ = _
  exact (paperSupportedMap_congr _ _ _ _ _ _ hh).trans hc.symm

set_option maxHeartbeats 800000 in
-- 支持部分圏と商の型に沿った群作用の比較に必要。
/-- 実際の係数変更から得られる、支持つき K₀ 上の群作用。 -/
noncomputable instance paperK0DistribMulAction :
    DistribMulAction G
      (TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) where
  smul g := paperTwistK0 (s := s) (T := T) z g
  one_smul x := by
    change paperTwistK0 (s := s) (T := T) z (1 : G) x = x
    exact DFunLike.congr_fun (paperTwistK0_one (s := s) (T := T) (G := G) z) x
  mul_smul g h x := by
    change paperTwistK0 (s := s) (T := T) z (g * h) x =
      paperTwistK0 (s := s) (T := T) z g (paperTwistK0 (s := s) (T := T) z h x)
    exact DFunLike.congr_fun (paperTwistK0_mul (s := s) (T := T) z g h) x
  smul_zero g := map_zero _
  smul_add g x y := map_add _ _ _

/-- 対象の類への作用は、その対象をひねった類である。 -/
lemma paperK0_smul_mk (g : G)
    (X : (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    g • TriangulatedK0.mk X = TriangulatedK0.mk ((paperTwist (T := T) z g).obj X) :=
  TriangulatedK0.map_mk _ _

end SerrePositivity.Asymptotic

end PaperTwistPart

section PaperComplexBaseChangePart

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 論文の商と計算側の商で、同じ複体列の支持条件は一致する。 -/
lemma paperComplex_supported_iff
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K) :
    paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) ↔
      scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) := by
  change scalarSupported z _ ↔ _
  rw [← scalarSupported_equivalence_iff (paperRankEquivalence R s) z]
  exact (scalarSupported z).prop_iff_of_iso ((paperSequenceComparison R s).app _)

/-- 行列の係数変更で得る具体的な複体列は、論文の商でも支持される。 -/
lemma paperChangedComplex_supported
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    paperSupportedRank (φ ∘ z) ((paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK))) := by
  obtain ⟨v, hv, hx⟩ := h
  apply (paperComplex_supported_iff (φ ∘ z) _ _).mpr
  exact ⟨v, hv, paperBaseChange_complex_smul_zero φ z K hK v hx⟩

/-- 抽象的な係数変更の像は、行列を係数変更した複体列の像と同型である。 -/
noncomputable def paperChangeRingComplexIso
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK))) :
    (paperSupportedChangeRing φ z).obj
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ ≅
    ⟨(paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)), paperChangedComplex_supported φ z K hK h⟩ := by
  let L := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K
  let hL := changeRing_strictlyBounded φ K hK
  let h' := paperChangedComplex_supported φ z K hK h
  let hc := (paperComplex_supported_iff (φ ∘ z) L hL).mp h'
  exact (paperSupportedRankEquivalence (φ ∘ z)).functor.preimageIso
    (paperBaseChangeComplexIso φ z K hK h hc ≪≫ (paperComplexComparison (φ ∘ z) L hL h').symm)

variable {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 係数変更の K₀ 写像と二つの支持部分圏の比較に必要。
/-- 係数変更後の Euler 評価を、別の支持の指定で同じ行列複体列上に計算できる。 -/
theorem paperBaseChangeEulerK0_complex_support_change
    {f : ℕ} (w : Fin f → S)
    (hJw : J ≤ (Ideal.span (Set.range w)).radical)
    (hfinw : ∀ v : ℕ, 0 < v → ∀ q,
      lam.len ((koszulComplex (fun j ↦ w j ^ v)).homology q) ≠ ⊤)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (hw : paperSupportedRank w ((paperSequenceFunctor S s).obj
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)))) :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) =
    paperRankEulerK0 lam hfg w hJw hfinw U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor S s).obj
        (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
          (changeRing_strictlyBounded φ K hK)), hw⟩) := by
  rw [paperBaseChangeEulerK0, AddMonoidHom.comp_apply]
  rw [TriangulatedK0.map_mk,
    TriangulatedK0.mk_iso (paperChangeRingComplexIso φ z K hK h)]
  exact paperRankEulerK0_complex_support_independent lam hfg (φ ∘ z) w hJ hJw hfin hfinw
    U hU hs _ _ _ hw

/-- 恒等係数変更後の評価は、元の支持圏の評価そのものである。 -/
lemma paperBaseChangeEulerK0_id {I : Ideal R} (mu : NormalizedLength R I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range z)).radical)
    (hfinite : ∀ v : ℕ, 0 < v → ∀ q,
      mu.len ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤) :
    paperBaseChangeEulerK0 (RingHom.id R) z mu hIfg hI hfinite U hU hs =
      paperRankEulerK0 mu hIfg z hI hfinite U hU hs := by
  simp only [paperBaseChangeEulerK0, paperSupportedChangeRingK0_id, AddMonoidHom.comp_id]
  rfl

end SerrePositivity.Asymptotic

end PaperComplexBaseChangePart

section OrdinaryTwistEvaluationPart

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

end OrdinaryTwistEvaluationPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Eq (4.2)" (partial := component) "仮定：厳密有界自由列で表された対象と恒等射を殺す共通のパラメータ冪（持ち上げの部分で一致）。結論：通常・係数拡大それぞれの Koszul 後の長さと二項係数による等式（式の一様台つき持ち上げ上の数値部分）。"] _root_.SerrePositivity.Asymptotic.paperBaseChangeBetti_koszul_formula
attribute [cite Paper "Eq (4.2)" (partial := component) "仮定：厳密有界自由列で表された対象と恒等射を殺す共通のパラメータ冪（持ち上げの部分で一致）。結論：通常・係数拡大それぞれの Koszul 後の長さと二項係数による等式（式の一様台つき持ち上げ上の数値部分）。"] _root_.SerrePositivity.Asymptotic.paperRankBetti_koszul_formula
attribute [cite Paper "Proof step §4.5 G-action" (partial := component) "仮定：有限群の T への A 線型作用と T 上の支持付きランク商（原典のスカラー捻り）。結論：スカラー捻りが支持付きランク商の K₀ 上で群作用を与え、生成元で捻りと一致（原典の作用の K₀ 成分）。"] _root_.SerrePositivity.Asymptotic.paperK0_smul_mk
attribute [cite Paper "Proof step §4.5 G-action" (partial := component) "仮定：有限群の T への A 線型作用と T 上の支持付きランク商（原典のスカラー捻り）。結論：スカラー捻りが支持付きランク商の K₀ 上で群作用を与え、生成元で捻りと一致（原典の作用の K₀ 成分）。"] _root_.SerrePositivity.Asymptotic.paperTwistK0_mul
attribute [cite Paper "Prop 4.3" (partial := component) "仮定：パラメータ冪の Koszul 長さと有限性、支持付きランク商の対象（同じ支持条件の実現）。結論：各次数の実数長さの非負性と K₀ での Euler 評価（原典の数値的結論。長さ零で割った二つのアーベル圏へのホモロジー関手は含まない）。"] _root_.SerrePositivity.Asymptotic.paperBaseChangeBetti_nonneg
attribute [cite Paper "Prop 4.3" (partial := component) "仮定：パラメータ冪の Koszul 長さと有限性、支持付きランク商の対象（同じ支持条件の実現）。結論：各次数の実数長さの非負性と K₀ での Euler 評価（原典の数値的結論。長さ零で割った二つのアーベル圏へのホモロジー関手は含まない）。"] _root_.SerrePositivity.Asymptotic.paperBaseChangeEulerK0_mk
attribute [cite Paper "Prop 4.3" (partial := component) "仮定：パラメータ冪の Koszul 長さと有限性、支持付きランク商の対象（同じ支持条件の実現）。結論：各次数の実数長さの非負性と K₀ での Euler 評価（原典の数値的結論。長さ零で割った二つのアーベル圏へのホモロジー関手は含まない）。"] _root_.SerrePositivity.Asymptotic.paperRankBetti_nonneg
attribute [cite Paper "Prop 4.3" (partial := component) "仮定：パラメータ冪の Koszul 長さと有限性、支持付きランク商の対象（同じ支持条件の実現）。結論：各次数の実数長さの非負性と K₀ での Euler 評価（原典の数値的結論。長さ零で割った二つのアーベル圏へのホモロジー関手は含まない）。"] _root_.SerrePositivity.Asymptotic.paperRankEulerK0_mk
