module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeTransitionPi
public import SerrePositivity.KST.NonConnective.DGSuspensionPerfectStructurePi

/-!
概要：実評価 Perf 比較による同じ懸垂列に、連結版 fiber 比較と自然な次数移動を適用する。
方針：元の構造辺の π 作用を同じ BF 構造射へ戻し、実隣接射と余錐の脚へ渡す。
規約：段別 I・P・Z と連結版 K-6 の非負次数比較に条件付き。Sp 引き戻し性は使わない。
使われ方：K-7 d3 の非負次数の安定化と、元の連結 K からの実比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance perfectTransitionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

private theorem perfectTransition_ofEq {x y x' y' : Sp.{w} _⦋0⦌}
    (e : Sp.Edge x y) (hx : x = x') (hy : y = y') (j : ℤ) :
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated) j) ↔
    Function.Bijective (SpectrumHo.piMap
      (Truncated.HomotopyCategory.homMk e.toTruncated) j) := by
  cases hx
  cases hy
  rfl

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (h : ∀ (n : ℕ) (k : ℤ), 0 ≤ k → Function.Bijective
    (dgConnectiveFiberComparisonPi R
      (dgKappaResolvedConnectiveSquare R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone)
      (dgKappaResolvedConnectiveSquare_zero_corner R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone (dgKappaResolvedNullPerf_isZero R
          (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone)) k).hom)

include h in
/-- 概要：段別連結版 fiber 比較に条件付きで、実隣接射は j+n 非負の範囲で π 同型。
方針：同じ実評価 Perf 比較による構造射へ自然な次数移動を適用する。
規約：元の I・P・Z と実零角を使い、Sp 引き戻し性は要求しない。
使われ方：K-7 d3 の同じ実反復列の隣接安定化。 -/
theorem dgSuspensionPerfectTransition_shifted_bijective (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j + n) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A
      (dgSuspensionResolvedConnectiveStructureEdge R s A Z
        (dgSuspensionResolvedPerfEquivalence R s A)) n) j) := by
  apply (dgSuspensionNativeSequenceMap_bijective_iff_structure R s A _ n j).mpr
  unfold dgSuspensionResolvedConnectiveStructureEdge dgSuspensionConnectiveStructureEdge
  apply (perfectTransition_ofEq _ _ _ (j + n)).mpr
  rw [SpectrumHo.piMap_edge]
  change Function.Bijective (OmegaSpectrum.homotopyMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _)) (j + n))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
  exact dgSuspensionPerfectStructureMap_shifted_bijective R s A Z h n j hj

include h in
/-- 概要：段別連結版 fiber 比較に条件付きで、元の連結 K 比較は全非負次数で π 同型。
方針：自然な次数移動による同じ実隣接射の安定化を、余錐の零段の脚へ渡す。
規約：段別入力と連結版 K-6 の条件を保持し、その供給の存在は主張しない。
使われ方：K-7 d3 の連結比較。Ind I-2 e との照合は別工程。 -/
theorem dgSuspensionPerfectConnectedComparison_nonnegative_bijective (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionPerfectConnectedComparison R s A Z) j) := by
  apply dgSuspensionConnectedComparison_bijective
  intro n
  exact dgSuspensionPerfectTransition_shifted_bijective R s A Z h n j (by omega)

/-- 概要：同じ実連結比較を順方向に持つ、非負整数次数の群同型。
方針：連結版 fiber 比較に条件付きの全単射性から群同型を作る。
規約：I・P・Z と K-6 の条件を保持する。
使われ方：連結 K と同じ非連結化候補の非負次数比較。 -/
def dgSuspensionPerfectConnectedComparison_nonnegativeEquiv (j : ℤ) (hj : 0 ≤ j) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R A) j ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionPerfectConnectiveCandidate R s A Z) j :=
  MulEquiv.ofBijective (OmegaSpectrum.homotopyMap
    (dgSuspensionPerfectConnectedComparison R s A Z) j)
    (dgSuspensionPerfectConnectedComparison_nonnegative_bijective R s A Z h j hj)

include h in
/-- 概要：同じ実 SOA 連結 K からの比較も全非負次数で π 同型。
方針：元の固定 K への公開 SOA 比較と、同じ余錐への実連結比較を合成する。
規約：段別 I・P・Z と連結版 K-6 の非負次数比較に条件付き。
使われ方：元の連結 K 模型との比較を同じ非連結化候補へ渡す。 -/
theorem dgSuspensionPerfectSOAConnectedComparison_nonnegative_bijective
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (presentedPerfectDGBFSOASpectrumComparison R A ≫
        dgSuspensionPerfectConnectedComparison R s A Z) j) := by
  rw [OmegaSpectrum.homotopyMap_comp]
  exact (dgSuspensionPerfectConnectedComparison_nonnegative_bijective R s A Z h j hj).comp
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R A j)

include h in
/-- 概要：任意整数次数で十分後の段から同じ実余錐への脚は π 同型。
方針：j+n 非負の末尾で隣接安定化を合成し、既存の群余極限の判定を使う。
規約：段別連結版 fiber 比較に条件付き。候補の負次数消滅は主張しない。
使われ方：K-7 d3 の負次数を含む候補の段別表示。 -/
theorem dgSuspensionPerfectCandidateLeg_tail_bijective (j : ℤ) (n : ℕ)
    (hn : (-j).toNat ≤ n) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (sequentialCandidateColimitLegHom
        (dgSuspensionPerfectConnectiveSequence R s A Z) ⟨n⟩) j) := by
  rw [sequentialCandidateColimitLeg_pi]
  apply sequentialInjection_bijective_of_stable _ j n
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have he : (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_refl n)) =
        𝟙 (⟨n⟩ : SequentialIndex.{max (u + 1) v}) := Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_id, OmegaSpectrum.homotopyMap_id]
    exact Function.bijective_id
  | succ m hm ih =>
    have he : (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ_of_le hm)) =
        homOfLE (X := SequentialIndex.{max (u + 1) v}) hm ≫
          homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ m) :=
      Subsingleton.elim _ _
    rw [he, CategoryTheory.Functor.map_comp, OmegaSpectrum.homotopyMap_comp]
    have hs : Function.Bijective (OmegaSpectrum.homotopyMap
        ((dgSuspensionPerfectConnectiveSequence R s A Z).map
          (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ m))) j) := by
      change Function.Bijective (OmegaSpectrum.homotopyMap
        ((dgSuspensionNativeSequence R s A _).map
          (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ m))) j)
      rw [dgSuspensionNativeSequence_map_succ]
      exact dgSuspensionPerfectTransition_shifted_bijective R s A Z h m j (by omega)
    exact hs.comp ih

/-- 概要：任意整数 j の候補の π を、十分後の元の懸垂 K の j+n 次数から比較する。
方針：同じ段の loop 次数比較の逆と、元の実余錐の脚の群同型を合成する。
規約：段別 I・P・Z と連結版 K-6 に条件付き。負群の消滅は主張しない。
使われ方：K-7 d の負次数の記述。 -/
def dgSuspensionPerfectCandidate_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionPerfectConnectiveCandidate R s A Z) j :=
  (dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm.trans
    (MulEquiv.ofBijective (OmegaSpectrum.homotopyMap
      (sequentialCandidateColimitLegHom (dgSuspensionPerfectConnectiveSequence R s A Z) ⟨n⟩) j)
      (dgSuspensionPerfectCandidateLeg_tail_bijective R s A Z h j n hn))

/-- 概要：十分後の段の群比較は、元の実隣接構造射を通っても同じ余錐の脚となる。
方針：同じ実余錐の π 群余錐の自然性を、元の次数座標へ読み戻す。
規約：段別連結版 fiber 比較に条件付き。別の遷移射や余錐は選ばない。
使われ方：K-7 d3 の全整数次数の段別表示を同じ実反復列へ照合する。 -/
theorem dgSuspensionPerfectCandidate_tailPiEquiv_succ (j : ℤ) (n : ℕ)
    (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n)) :
    dgSuspensionPerfectCandidate_tailPiEquiv R s A Z h j (n + 1)
        (Nat.le_succ_of_le hn)
        (dgSuspensionShiftedTransition R s A
          (dgSuspensionResolvedConnectiveStructureEdge R s A Z
            (dgSuspensionResolvedPerfEquivalence R s A)) n j x) =
      dgSuspensionPerfectCandidate_tailPiEquiv R s A Z h j n hn x := by
  let D := dgSuspensionPerfectConnectiveSequence R s A Z
  have he := (sequentialCandidatePiCocone D j).ι.naturality
    (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n))
  have hx := congrArg (fun f => f.hom
    ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)) he
  change OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D ⟨n + 1⟩) j
    (OmegaSpectrum.homotopyMap (D.map (homOfLE
      (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n))) j
      ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)) =
    OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D ⟨n⟩) j
      ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x) at hx
  simp only [dgSuspensionPerfectCandidate_tailPiEquiv, dgSuspensionShiftedTransition,
    MulEquiv.trans_apply, MulEquiv.ofBijective_apply, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply,
    D, dgSuspensionPerfectConnectiveCandidate, dgSuspensionPerfectConnectiveSequence,
    dgSuspensionResolvedConnectiveSequence,
    dgSuspensionNativeSequence_map_succ] at hx ⊢
  convert hx using 1

end SerrePositivity.KST.NonConnective
