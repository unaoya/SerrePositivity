module

public import SerrePositivity.HomologicalAlgebra.MinimalResolution
public import SerrePositivity.Asymptotic.Minimal
public import SerrePositivity.Paper.Section4.RankQuotient
public import SerrePositivity.HomologicalAlgebra.KoszulTruncation
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.CategoryTheory.IteratedCone
public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.LengthAlgebra.Koszul
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # 極小分解による Euler の下界

## 概要

極小分解の切り詰めがランク商で台を持ち、切り詰めの深さによらないことを示し、極小分解の正規化極限とランク商の Betti 評価を比べる。係数変更の後の Euler の下界、K₀ のひねりと係数変更の合成、共役ごとの Euler の下界、局所的な係数変更の後の振幅・極小性と共役の下界を与える。実際のテンソル Koszul 複体の振幅と共通の反復錐定理から、係数変更の後のホモロジーの消滅も与える（λ-平坦性の変種 `Section4/SymmetricComparison` が使う）。

## 方針

比べる次数ごとに切り詰めを深くするので、切り詰めの境界に台は要求しない。局所環の自己同型は極大イデアルを保つので、全共役の下界のイデアルの条件は一つの条件から従う。

## 規約

論文の §4・§5 の下界の議論に固有なので Paper/Section4 に置く（Asymptotic の Minimal の一部は論文の結果を使うので、こちらへ移した）。

## 使われ方

Paper/Section5 の正値性と近似。
-/

@[expose] public noncomputable section

universe u

section MinimalSupportPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits IsLocalRing Filter Asymptotics

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {s : ℕ → ℕ} (M : ℕ → FGModuleCat.{u} R) (l : ℕ)

/-- 直前の Betti 数の `o(s)` は境界複体の全項の `o(s)` を与える。 -/
lemma minimal_boundary_rank_isLittleO
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) (q : ℤ) :
    (fun n ↦ (Module.finrank R ((MinimalFreeResolution.boundary (M n) l).X q) : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  by_cases hq : q = -(l : ℤ)
  · subst q
    simp_rw [MinimalFreeResolution.boundary_finrank]
    exact minimal_rank_isLittleO M (l + 1) hsmall
  · apply (isLittleO_zero (fun n ↦ (s n : ℝ)) atTop).congr_left
    intro n
    have := ModuleCat.subsingleton_of_isZero
      (MinimalFreeResolution.boundary_isZero_X (M n) l q hq)
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]

/-- 境界の族を、小さいランクの実際の自由複体列に組み戻す。 -/
lemma exists_minimal_boundary_sequence
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ G : CochainComplex (FreeSequence R s) ℤ,
      rankSmallComplex G ∧ ∀ n,
        Nonempty ((evaluateComplex n).obj G ≅ MinimalFreeResolution.boundary (M n) l) := by
  let P (n : ℕ) := MinimalFreeResolution.boundary (M n) l
  let r (q : ℤ) (n : ℕ) := Module.finrank R ((P n).X q)
  have hr (q : ℤ) : (fun n ↦ (r q n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)) :=
    minimal_boundary_rank_isLittleO M l hsmall q
  let e (n : ℕ) (q : ℤ) : ModuleCat.of R (Fin (r q n) → R) ≅ (P n).X q :=
    (Module.finBasis R ((P n).X q)).equivFun.toModuleIso.symm
  refine ⟨assembleComplex P r (fun q ↦ (hr q).isBigO) e,
    assembleComplex_rankSmall P r _ e (-(l : ℤ)) (-(l : ℤ)) ?_ hr,
    fun n ↦ ⟨evaluateAssembleIso P r _ e n⟩⟩
  intro n q hq
  exact MinimalFreeResolution.boundary_isZero_X (M n) l q (by omega)

/-- 共通の消去元は、切り詰めた列の論文のランク商での像を消す。 -/
lemma minimal_truncated_paper_scalar_zero
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (r : R) (hM : ∀ n, r • 𝟙 (M n).obj = 0) :
    r • 𝟙 ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) = 0 := by
  obtain ⟨G, hG, heG⟩ := exists_minimal_boundary_sequence M l hsmall
  have hf : ∀ n, ∃ (u : (evaluateComplex n).obj K ⟶ (evaluateComplex n).obj G)
      (v : (evaluateComplex n).obj G ⟶ (evaluateComplex n).obj K),
      Nonempty (Homotopy (r • 𝟙 _) (u ≫ v)) := by
    intro n
    obtain ⟨e⟩ := he n
    obtain ⟨eG⟩ := heG n
    obtain ⟨u, v, ⟨h⟩⟩ := MinimalFreeResolution.scalar_boundary_factorization (M n) l r (hM n)
    refine ⟨e.hom ≫ u ≫ eG.inv, eG.hom ≫ v ≫ e.inv, ?_⟩
    have ht := (h.compRight e.inv).compLeft e.hom
    simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc] using (Nonempty.intro ht)
  obtain ⟨u, v, ⟨h⟩⟩ := assemble_scalar_factorization K G r hf
  exact paper_scalar_zero_of_small_factorization K G hK hG r u v h

/-- 共通の正の消去指数は、切り詰めの後もランク商での支持を与える。 -/
lemma minimal_truncated_paper_supported {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hsmall : (fun n ↦ ((Module.length R
      (TorModule R (l + 1) (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (N : ℕ) (hN : 0 < N) (hM : ∀ n j, z j ^ N • 𝟙 (M n).obj = 0) :
    paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)) :=
  ⟨N, hN, fun j ↦ minimal_truncated_paper_scalar_zero M l K hK he hsmall
    (z j ^ N) (fun n ↦ hM n j)⟩

end SerrePositivity.Asymptotic

end MinimalSupportPart

section MinimalTruncationComparisonPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits IsLocalRing Filter Asymptotics StupidTruncation

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {s : ℕ → ℕ} (M : ℕ → FGModuleCat.{u} R)

/-- 各段との同型から、自由列の階数と極小分解の階数を直接比較する。 -/
lemma rank_eq_truncated_finrank (m : ℕ) (K : CochainComplex (FreeSequence R s) ℤ)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) m))
    (q : ℤ) (n : ℕ) :
    (K.X q).rank n = Module.finrank R ((MinimalFreeResolution.truncated (M n) m).X q) := by
  obtain ⟨e⟩ := he n
  have h := ((HomologicalComplex.eval _ _ q).mapIso e).toLinearEquiv.finrank_eq
  change Module.finrank R (Fin ((K.X q).rank n) → R) =
    Module.finrank R ((MinimalFreeResolution.truncated (M n) m).X q) at h
  simpa only [Module.finrank_fin_fun] using h

/-- 高次 Betti 数が小さい範囲で、深い切り詰めの尾部は小さいランクをもつ。 -/
lemma minimal_truncated_tail_small (l m : ℕ)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (he : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) m))
    (hsmall : ∀ i, l < i → i ≤ m →
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) :
    ∀ q < -(l : ℤ), (fun n ↦ ((K.X q).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)) := by
  intro q hq
  simp_rw [rank_eq_truncated_finrank M m K he]
  by_cases hqm : q < -(m : ℤ)
  · apply (isLittleO_zero (fun n ↦ (s n : ℝ)) atTop).congr_left
    intro n
    have := ModuleCat.subsingleton_of_isZero
      (MinimalFreeResolution.truncated_isZero_X (M n) m q (.inl hqm))
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  · have heq : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    have him : (-q).toNat ≤ m := by omega
    have hil : l < (-q).toNat := by omega
    conv_lhs => rw [heq]
    simp_rw [MinimalFreeResolution.truncated_finrank _ m _ him]
    exact minimal_rank_isLittleO M (-q).toNat (hsmall _ hil him)

/-- 深い切り詰めを浅く切ると、最初から浅く切ったモデルと鎖同型になる。 -/
noncomputable def minimalTruncatedAboveIso (l m : ℕ) (hlm : l ≤ m)
    (K L : CochainComplex (FreeSequence R s) ℤ)
    (eK : ∀ n, (evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l)
    (eL : ∀ n, (evaluateComplex n).obj L ≅ MinimalFreeResolution.truncated (M n) m) :
    above L (-(l : ℤ)) ≅ K :=
  assembleComplexIso (fun n ↦ mapAboveIso (FreeSequence.evaluation n) L (-(l : ℤ)) ≪≫
    ((ComplexShape.embeddingUpIntGE (-(l : ℤ))).stupidTruncFunctor _).mapIso (eL n) ≪≫
    aboveAboveIso (extRes (MinimalFreeResolution.resolution (M n)))
      (-(l : ℤ)) (-(m : ℤ)) (by omega) ≪≫ (eK n).symm)

/-- Betti 数が小さい範囲で切り詰めの深さを変えても、論文のランク商の対象は同じ。 -/
noncomputable def minimalTruncationsPaperIso (l m : ℕ) (hlm : l ≤ m)
    (K L : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K) (hL : strictlyBoundedComplex _ L)
    (eK : ∀ n, (evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l)
    (eL : ∀ n, (evaluateComplex n).obj L ≅ MinimalFreeResolution.truncated (M n) m)
    (hsmall : ∀ i, l < i → i ≤ m →
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) :
    (paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK) ≅
      (paperSequenceFunctor R s).obj (sequenceHomotopyObj L hL) :=
  ((paperSequenceFunctor R s).mapIso
    (show sequenceHomotopyObj (above L (-(l : ℤ))) (above_bounded L hL _) ≅
      sequenceHomotopyObj K hK from
      ObjectProperty.isoMk _ ((HomotopyCategory.quotient _ _).mapIso
        (minimalTruncatedAboveIso M l m hlm K L eK eL)))).symm ≪≫
    paperTruncationIso L hL (-(l : ℤ))
      (minimal_truncated_tail_small M l m L (fun n ↦ ⟨eL n⟩) hsmall)

/-- 残す項の `O(s)` と追加する項の `o(s)` から、同じ商の対象を表す深い切り詰めを構成する。 -/
theorem exists_deeper_minimal_truncation (l m : ℕ) (hlm : l ≤ m)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hbetti : ∀ i ≤ l,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (hsmall : ∀ i, l < i → i ≤ m →
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ))) :
    ∃ L : CochainComplex (FreeSequence R s) ℤ,
      ∃ hb : L.IsStrictlyGE (-(m : ℤ)) ∧ L.IsStrictlyLE 0,
      (∀ n, Nonempty ((evaluateComplex n).obj L ≅ MinimalFreeResolution.truncated (M n) m)) ∧
      Nonempty ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK) ≅
        (paperSequenceFunctor R s).obj (sequenceHomotopyObj L ⟨-(m : ℤ), 0, hb.1, hb.2⟩)) := by
  classical
  have hO (i : ℕ) (hi : i ≤ m) :
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)) := by
    by_cases hil : i ≤ l
    · exact hbetti i hil
    · exact (hsmall i (by omega) hi).isBigO
  obtain ⟨L, hb, eL, _, _⟩ := exists_minimal_truncated_sequence M m hO
  exact ⟨L, hb, eL, ⟨minimalTruncationsPaperIso M l m hlm K L hK _
    (fun n ↦ (eK n).some) (fun n ↦ (eL n).some) hsmall⟩⟩

/-- 任意の整数次数で、下端より上の Koszul ホモロジーを全分解と比較する。 -/
noncomputable def minimalModelKoszulHomologyIsoAt {S : Type u} [CommRing S] (φ : R →+* S)
    (l : ℕ) (K : CochainComplex (FreeSequence R s) ℤ)
    (eK : ∀ n, (evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l)
    {e : ℕ} (x : Fin e → S) (q : ℤ) (hq : -(l : ℤ) < q) (n : ℕ) :
    (koszulComplexOn x (baseChange φ ((evaluateComplex n).obj K))).homology q ≅
      (koszulComplexOn x (baseChange φ
        (extRes (MinimalFreeResolution.resolution (M n))))).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((koszulFunctor x).mapIso
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).mapIso (eK n))) ≪≫
    StupidTruncation.koszulMapHomologyIso (ModuleCat.extendScalars φ) x _ _ q hq

end SerrePositivity.Asymptotic

end MinimalTruncationComparisonPart

section MinimalBettiEvaluationPart

namespace SerrePositivity.Asymptotic

open CategoryTheory Limits Filter Asymptotics IsLocalRing

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing S] (φ : R →+* S)

/-- 極小分解全体を係数変更した複体。一般には下に非有界である。 -/
noncomputable abbrev minimalBaseChangeResolution (M : FGModuleCat.{u} R) :=
  baseChange φ (extRes (MinimalFreeResolution.resolution M))

/-- 加群の消去元は、係数変更した全分解でも零ホモトピックに作用する。 -/
lemma minimalBaseChangeResolution_null (M : FGModuleCat.{u} R) (a : R)
    (ha : a • 𝟙 M.obj = 0) :
    Nonempty (Homotopy (smulId (φ a) (minimalBaseChangeResolution φ M)) 0) := by
  have h := (ModuleCat.extendScalars φ).mapHomotopy
    (resolutionScalarNullHomotopy (MinimalFreeResolution.resolution M) a ha)
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h
  exact ⟨h⟩

variable [Nontrivial S] {s : ℕ → ℕ} (M : ℕ → FGModuleCat.{u} R)
  {e : ℕ} (z : Fin e → R) {J : Ideal S} (lam : NormalizedLength S J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q,
    lam.len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤)

omit [Nontrivial S] in
include hfg hJ hfin in
/-- 全分解の各次数の長さは有限で `O(s)`。有限性を新しい入力にせず、
深い有限自由モデルの Koszul 評価と、その直和因子への上界から導く。 -/
lemma minimalBaseChangeResolution_length_bound
    (hbetti : ∀ i,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0) (q : ℤ) :
    (∀ n, lam.len ((minimalBaseChangeResolution φ (M n)).homology q) ≠ ⊤) ∧
    (fun n ↦ (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  let m := (-q).toNat + 1
  obtain ⟨L, hb, eL, _, _⟩ := exists_minimal_truncated_sequence M m (fun i _ ↦ hbetti i)
  let hL : strictlyBoundedComplex _ L := ⟨-(m : ℤ), 0, hb.1, hb.2⟩
  let L' := ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj L
  let hL' := changeRing_strictlyBounded φ L hL
  let x : Fin e → S := fun j ↦ φ (z j) ^ v
  have hJ' : J ≤ (Ideal.span (Set.range x)).radical := le_radical_span_pow (φ ∘ z) hJ v
  have hnull (n : ℕ) (j : Fin e) : Nonempty
      (Homotopy (smulId (x j) (minimalBaseChangeResolution φ (M n))) 0) := by
    simpa only [map_pow] using minimalBaseChangeResolution_null φ (M n) (z j ^ v) (hM n j)
  let P := fun n ↦ minimalBaseChangeResolution φ (M n)
  have hlen (n : ℕ) : lam.len ((koszulComplexOn x (P n)).homology q) =
      lam.len ((koszulComplexOn x ((evaluateComplex n).obj L')).homology q) := by
    apply lam.len_congr _ _
    exact ((minimalModelKoszulHomologyIsoAt M φ m L (fun n ↦ (eL n).some) x q
      (by dsimp [m]; omega) n).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ q).mapIso
        ((koszulFunctor x).mapIso (FreeSequence.evaluateComplexTensorIso φ n L))).toLinearEquiv
  have hkfin (n : ℕ) : lam.len ((koszulComplexOn x (P n)).homology q) ≠ ⊤ := by
    rw [hlen]
    exact sequenceKoszulHomology_ne_top lam hfg x hJ' (hfin v hv) L' hL' n q
  have hkO : (fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
    simp_rw [hlen]
    exact sequenceKoszulHomology_isBigO lam hfg x hJ' (hfin v hv) L' hL' q
  have hle (n : ℕ) : lam.len ((P n).homology q) ≤
      lam.len ((koszulComplexOn x (P n)).homology q) := by
    let r := (retractKoszulComplexOn x (P n) (hnull n)).map
      (HomologicalComplex.homologyFunctor _ _ q)
    exact lam.len_le_of_injective r.i.hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
      (supported_homology_isPowTorsion hfg hJ' (isSupported_koszulComplexOn x (P n)) q)
  refine ⟨fun n ↦ ne_top_of_le_ne_top (hkfin n) (hle n), ?_⟩
  apply IsBigO.trans (g := fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal) ?_ hkO
  apply IsBigO.of_norm_le
  intro n
  simp only [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (hkfin n) (hle n)

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

set_option maxHeartbeats 800000 in
-- 支持つき商の係数変更と、代表の同型による評価の移送を同時に簡約するため。
/-- 高次 Betti 数が `o(s)` で、加群列に共通の消去冪があれば、ランク商の評価は
全極小分解のホモロジー長の正規化極限と一致する。元の切り詰めの一様支持は不要。 -/
theorem paperBaseChangeBetti_eq_minimal_homology_limit
    (l : ℕ) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
    (hbetti : ∀ i ≤ l,
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)))
    (hsmall : ∀ i, l < i →
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =o[atTop] (fun n ↦ (s n : ℝ)))
    (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
    (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0) (q : ℤ) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ q =
    normalizedLimit U s (fun n ↦
      (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal) := by
  let P := fun n ↦ minimalBaseChangeResolution φ (M n)
  let X : (paperSupportedRank (s := s) z).FullSubcategory :=
    ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩
  have hall (i : ℕ) :
      (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
        =O[atTop] (fun n ↦ (s n : ℝ)) := by
    by_cases hi : i ≤ l
    · exact hbetti i hi
    · exact (hsmall i (by omega)).isBigO
  have hbound := minimalBaseChangeResolution_length_bound φ M z lam hfg hJ hfin hall v hv hM
  have hnull (n : ℕ) (j : Fin e) : Nonempty
      (Homotopy (smulId (φ (z j) ^ v) (P n)) 0) := by
    simpa only [map_pow] using minimalBaseChangeResolution_null φ (M n) (z j ^ v) (hM n j)
  have ht (n : ℕ) (q : ℤ) : IsPowTorsion J ((P n).homology q) :=
    supported_homology_isPowTorsion hfg hJ (show IsSupported (φ ∘ z) (P n) from
      ⟨v, hnull n⟩) q
  have heq : paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs X =
      fun q ↦ normalizedLimit U s (fun n ↦ (lam.len ((P n).homology q)).toReal) := by
    apply coneLength_binomial_cancel_of_hasFiniteSupport e _ _
      (paperBaseChangeBetti_hasFiniteSupport φ z lam hfg hJ hfin U hU hs X) 1
    · intro q hq
      have hz (n : ℕ) : (lam.len ((P n).homology q)).toReal = 0 := by
        have hx : IsZero ((P n).X q) := (ModuleCat.extendScalars φ).map_isZero
          (extRes_isZero_X (MinimalFreeResolution.resolution (M n)) q (by omega))
        have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X (P n) q hx)
        rw [lam.len_eq_zero_of_subsingleton, ENNReal.toReal_zero]
      simp_rw [hz]
      exact normalizedLimit_zero U s
    · intro q
      let m := max l ((-q).toNat + 1)
      obtain ⟨L, hb, eL, ⟨iKL⟩⟩ := exists_deeper_minimal_truncation M l m (le_max_left _ _)
        K hK eK hbetti (fun i hi _ ↦ hsmall i hi)
      let hL : strictlyBoundedComplex _ L := ⟨-(m : ℤ), 0, hb.1, hb.2⟩
      have h' := (scalarSupported z).prop_of_iso iKL h
      have hx (j : Fin e) : z j ^ v • 𝟙
          ((paperSequenceFunctor R s).obj (sequenceHomotopyObj L hL)) = 0 :=
        minimal_truncated_paper_scalar_zero M m L hL eL
          (hsmall (m + 1) (by dsimp [m]; omega)) (z j ^ v) (fun n ↦ hM n j)
      have hi (r : ℤ) := paperBaseChangeBetti_iso φ z lam hfg hJ hfin U hU hs
        (show X ≅ ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj L hL), h'⟩ from
          ObjectProperty.isoMk _ iKL) r
      have hformula := paperBaseChangeBetti_koszul_formula φ z lam hfg hJ hfin U hU hs
        L hL h' v hv hx (-q)
      simp only [neg_sub, sub_neg_eq_add, add_comm] at hformula
      have hlen (n : ℕ) : lam.len
          ((koszulComplexOn (fun j ↦ φ (z j) ^ v)
            (baseChange φ ((evaluateComplex n).obj L))).homology (- -q)) =
          lam.len ((koszulComplexOn (fun j ↦ φ (z j) ^ v) (P n)).homology q) := by
        apply lam.len_congr _ _
        exact (eqToIso (congrArg (fun r : ℤ ↦
          (koszulComplexOn (fun j ↦ φ (z j) ^ v)
            (baseChange φ ((evaluateComplex n).obj L))).homology r) (neg_neg q)) ≪≫
          minimalModelKoszulHomologyIsoAt M φ m L
            (fun n ↦ (eL n).some) _ q (by dsimp [m]; omega) n).toLinearEquiv
      simp_rw [← hi, hlen] at hformula
      rw [← hformula]
      exact normalizedLimit_koszul_null_binomial lam _ P hnull ht
        (fun n q ↦ (hbound q).1 n) U hU s hs (fun q ↦ (hbound q).2) q
  exact congrFun heq q

variable (l : ℕ) (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (eK : ∀ n, Nonempty ((evaluateComplex n).obj K ≅ MinimalFreeResolution.truncated (M n) l))
  (hbetti : ∀ i ≤ l,
    (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =O[atTop] (fun n ↦ (s n : ℝ)))
  (hsmall : ∀ i, l < i →
    (fun n ↦ ((Module.length R (TorModule R i (M n) (R ⧸ maximalIdeal R))).toNat : ℝ))
      =o[atTop] (fun n ↦ (s n : ℝ)))
  (h : paperSupportedRank z ((paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v) (hM : ∀ n j, z j ^ v • 𝟙 (M n).obj = 0)

include eK hbetti hsmall hv hM in
/-- 商の各次数の評価を、代数係数の Tor の正規化極限として計算する。 -/
theorem paperBaseChangeBetti_eq_minimal_tor_limit (i : ℕ) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ (-(i : ℤ)) =
    normalizedLimit U s (fun n ↦ (lam.len (TorAlg φ i (M n))).toReal) := by
  rw [paperBaseChangeBetti_eq_minimal_homology_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]
  congr 1
  funext n
  let e := torIsoCochain φ (isResolutionOf_extRes (MinimalFreeResolution.resolution (M n))) i
  exact congrArg ENNReal.toReal (lam.len_congr _ _ e.toLinearEquiv.symm)

include eK hbetti hsmall hv hM in
/-- 極小分解から構成した対象は、係数変更後も正の cochain 次数の評価が零。 -/
lemma paperBaseChangeBetti_minimal_eq_zero_of_pos (q : ℤ) (hq : 0 < q) :
    paperBaseChangeBetti φ z lam hfg hJ hfin U hU hs
      ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩ q = 0 := by
  rw [paperBaseChangeBetti_eq_minimal_homology_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]
  have hz (n : ℕ) :
      (lam.len ((minimalBaseChangeResolution φ (M n)).homology q)).toReal = 0 := by
    have hx := (ModuleCat.extendScalars φ).map_isZero
      (extRes_isZero_X (MinimalFreeResolution.resolution (M n)) q hq)
    have := ModuleCat.subsingleton_of_isZero
      (isZero_homology_of_isZero_X (minimalBaseChangeResolution φ (M n)) q hx)
    rw [lam.len_eq_zero_of_subsingleton, ENNReal.toReal_zero]
  simp_rw [hz]
  exact normalizedLimit_zero U s

include eK hbetti hsmall hv hM in
/-- 商の Euler 評価は、Tor の各次数の正規化極限の交代和である。
各段の Euler 数との極限交換は主張せず、商で有限支持になった係数を足し合わせる。 -/
theorem paperBaseChangeEulerK0_eq_minimal_tor_limits :
    paperBaseChangeEulerK0 φ z lam hfg hJ hfin U hU hs
      (TriangulatedK0.mk ⟨(paperSequenceFunctor R s).obj (sequenceHomotopyObj K hK), h⟩) =
    ∑ᶠ i : ℕ, (-1 : ℝ) ^ i *
      normalizedLimit U s (fun n ↦ (lam.len (TorAlg φ i (M n))).toReal) := by
  rw [paperBaseChangeEulerK0_mk, alternating_finsum_eq_nat _
    (paperBaseChangeBetti_minimal_eq_zero_of_pos φ M z lam hfg hJ hfin U hU hs
      l K hK eK hbetti hsmall h v hv hM)]
  congr 1
  funext i
  rw [paperBaseChangeBetti_eq_minimal_tor_limit φ M z lam hfg hJ hfin U hU hs
    l K hK eK hbetti hsmall h v hv hM]

end SerrePositivity.Asymptotic

end MinimalBettiEvaluationPart

section PaperMinimalLowerBoundPart

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

end PaperMinimalLowerBoundPart

section PaperTwistLowerBoundPart

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
      φ ∘ algebraMap A R ∘ a :=
  congrArg (fun f : Fin e → R => φ ∘ f)
    (funext fun j ↦ (MulSemiringAction.toAlgHom A R g).commutes (a j))

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

end PaperTwistLowerBoundPart

section LocalBaseChangeBoundsPart

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

end LocalBaseChangeBoundsPart

section PaperVanishingPart

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

end SerrePositivity.Asymptotic

end PaperVanishingPart
