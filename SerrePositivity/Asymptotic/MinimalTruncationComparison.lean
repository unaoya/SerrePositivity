module

public import SerrePositivity.Asymptotic.TruncationComparison
public import SerrePositivity.Asymptotic.MinimalResolutionFamily
public import SerrePositivity.HomologicalAlgebra.KoszulTruncation

/-! # 極小分解の切り詰めの深さに依存しないランク商の対象

下端より高次の Betti 数が小さければ、計算したい次数に合わせて切り詰めを深くできる。
任意に選んだ基底で構成した複体列同士を、各段の鎖同型を組み戻して比較する。
-/

@[expose] public section

universe u

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
