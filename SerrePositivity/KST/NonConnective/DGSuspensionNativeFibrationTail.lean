module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeFibrationSequence
public import SerrePositivity.KST.NonConnective.SequentialCandidateTail
public import SerrePositivity.KST.NonConnective.DGSuspensionLoopStagePi

/-!
概要：採用経路による同じ実候補の任意整数 π を、十分後の元の懸垂段で表示する。
方針：元の実隣接射の移動後の非負次数比較を、同じ実余錐の末尾の脚へ渡す。
規約：段別 I、実 fibration 辺・非負次数比較、共終性に条件付き。負群消滅は主張しない。
使われ方：K-7 d3 の同じ非連結化候補の段別 π 表示。
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
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance nativeFibrationTailSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (ρ : ∀ n : ℕ, Sp.{max (u + 1) v}.Edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (stableCategoryModel
      (dgKappaNativeKernelCategory R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone))))
    ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (stableCategoryModel
        (dgKappaNativeSuspensionCategory R (dgSuspensionIteration R s A n)
          (dgSuspensionIterationStage R s A n).cone))))))

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (hρ : ∀ (n : ℕ) (j : ℤ), 0 ≤ j → Function.Bijective
    (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk (ρ n).toTruncated) j))


include hcofinal hρ in
/-- 概要：同じ実 fibration と共終性に条件付きで、十分後の段の実余錐の脚は任意整数 π 同型。
方針：移動した次数が非負になる同じ末尾の隣接安定化を元の実脚へ適用する。
規約：元の段と元の実 Sp 余錐を保持し、負群消滅は主張しない。
使われ方：K-7 d3 の任意整数次数の段別表示。 -/
theorem dgSuspensionNativeFibrationCandidateLeg_tail_bijective (j : ℤ) (n : ℕ)
    (hn : (-j).toNat ≤ n) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (sequentialCandidateColimitLegHom
        (dgSuspensionNativeSequence R s A (dgSuspensionNativeFibrationStructureEdge R s A ρ)) ⟨n⟩) j) := by
  apply sequentialCandidateLeg_bijective_of_adjacent_tail
  intro m hm
  rw [dgSuspensionNativeSequence_map_succ]
  exact dgSuspensionNativeFibrationTransition_bijective R s A ρ hcofinal hρ m j (by omega)

/-- 概要：同じ元の実候補の任意整数 π を、十分後の同じ実懸垂 K の移動次数から比較する。
方針：同じ段の loop 次数座標と、元の実余錐の同じ脚の群同型を合成する。
規約：実 fibration と共終性に条件付き。別の実余錐や遷移射を選ばない。
使われ方：K-7 d3 の非連結化候補の全整数群の段別表示。 -/
def dgSuspensionNativeFibrationCandidate_tailPiEquiv (j : ℤ) (n : ℕ)
    (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionNativeCandidate R s A
        (dgSuspensionNativeFibrationStructureEdge R s A ρ)) j :=
  (dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm.trans
    (MulEquiv.ofBijective (OmegaSpectrum.homotopyMap
      (sequentialCandidateColimitLegHom
        (dgSuspensionNativeSequence R s A (dgSuspensionNativeFibrationStructureEdge R s A ρ)) ⟨n⟩) j)
      (dgSuspensionNativeFibrationCandidateLeg_tail_bijective R s A ρ hcofinal hρ j n hn))

/-- 概要：十分後の段別 π 表示は、同じ元の隣接構造射を通っても同じ実余錐の脚となる。
方針：元の実余錐の π 群余錐の自然性を、同じ loop 次数座標へ戻す。
規約：同じ実 fibration と共終性に条件付き。別の遷移射へ置き換えない。
使われ方：K-7 d3 の全整数群の段別表示と元の反復構造射の整合。 -/
theorem dgSuspensionNativeFibrationCandidate_tailPiEquiv_succ (j : ℤ) (n : ℕ)
    (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n)) :
    dgSuspensionNativeFibrationCandidate_tailPiEquiv R s A ρ hcofinal hρ j (n + 1)
        (Nat.le_succ_of_le hn)
        (dgSuspensionShiftedTransition R s A
          (dgSuspensionNativeFibrationStructureEdge R s A ρ) n j x) =
      dgSuspensionNativeFibrationCandidate_tailPiEquiv R s A ρ hcofinal hρ j n hn x := by
  let C := dgSuspensionNativeSequence R s A (dgSuspensionNativeFibrationStructureEdge R s A ρ)
  have he := (sequentialCandidatePiCocone C j).ι.naturality
    (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n))
  have hx := congrArg (fun f => f.hom
    ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)) he
  change OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom C ⟨n + 1⟩) j
    (OmegaSpectrum.homotopyMap (C.map (homOfLE
      (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n))) j
      ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x)) =
    OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom C ⟨n⟩) j
      ((dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm x) at hx
  simp only [dgSuspensionNativeFibrationCandidate_tailPiEquiv, dgSuspensionShiftedTransition,
    MulEquiv.trans_apply, MulEquiv.ofBijective_apply, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply,
    C, dgSuspensionNativeSequence_map_succ] at hx ⊢
  convert hx using 1

end SerrePositivity.KST.NonConnective
