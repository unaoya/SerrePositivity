module
public import SerrePositivity.KST.NonConnective.DGSuspensionLoopStagePi
public import SerrePositivity.KST.NonConnective.DGSuspensionConnectedComparison

/-!
概要：元の実隣接 BF 遷移を、同じ懸垂段の整数 π の移動した座標へ読み替える。
方針：同じ段比較同型で実遷移を共役し、元の作用との可換性と全単射性の同値を保持する。
規約：明示構造辺に条件付き。元の構造辺の次数移動との自然性や安定化をこの定義だけで結論しない。
使われ方：K-7 d2・d3。実遷移の安定化と同じ実余錐の連結比較を接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance shiftedTransitionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance shiftedTransitionSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (β : ∀ n : ℕ,
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
      (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex
          (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))))

/-- 明示構造辺に条件付きで、同じ実隣接遷移を元の懸垂 K の移動した整数次数に表示する。 -/
def dgSuspensionShiftedTransition (n : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) →*
      OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1)))
        (j + (n + 1 : ℕ)) :=
  (dgSuspensionNativeSequenceStage_piEquiv R s A (n + 1) j).toMonoidHom.comp
    ((OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j).comp
      (dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm.toMonoidHom)

/-- 明示構造辺に条件付きで、次数座標の読み替えは同じ元の BF 射の実 π 作用と可換。 -/
theorem dgSuspensionShiftedTransition_comm (n : ℕ) (j : ℤ)
    (x : OmegaSpectrum.homotopyGroup (dgSuspensionNativeSequenceStage R s A n) j) :
    dgSuspensionShiftedTransition R s A β n j
        (dgSuspensionNativeSequenceStage_piEquiv R s A n j x) =
      dgSuspensionNativeSequenceStage_piEquiv R s A (n + 1) j
        (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j x) := by
  simp only [dgSuspensionShiftedTransition, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply]

/-- 明示構造辺に条件付きで、移動した座標上の全単射性は同じ元の実隣接遷移の全単射性と同値。 -/
theorem dgSuspensionShiftedTransition_bijective_iff (n : ℕ) (j : ℤ) :
    Function.Bijective (dgSuspensionShiftedTransition R s A β n j) ↔
      Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j) := by
  change Function.Bijective
    ((dgSuspensionNativeSequenceStage_piEquiv R s A (n + 1) j) ∘
      ((OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j) ∘
        (dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm)) ↔ _
  exact ((dgSuspensionNativeSequenceStage_piEquiv R s A (n + 1) j).bijective.of_comp_iff' _).trans
    (Function.Bijective.of_comp_iff _ (dgSuspensionNativeSequenceStage_piEquiv R s A n j).symm.bijective)

/-- 明示構造辺と移動座標の非負次数安定化に条件付きで、同じ実連結比較は非負次数 π 同型。 -/
theorem dgSuspensionConnectedComparison_bijective_of_shifted
    (h : ∀ (j : ℤ), 0 ≤ j → ∀ n : ℕ,
      Function.Bijective (dgSuspensionShiftedTransition R s A β n j))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionConnectedComparison R s A β) j) := by
  apply dgSuspensionConnectedComparison_bijective
  intro n
  exact (dgSuspensionShiftedTransition_bijective_iff R s A β n j).mp (h j hj n)

end SerrePositivity.KST.NonConnective
