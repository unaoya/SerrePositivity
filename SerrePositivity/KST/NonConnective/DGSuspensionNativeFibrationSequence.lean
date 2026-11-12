module
public import SerrePositivity.KST.NonConnective.DGKappaNativeStructure
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeTransitionPi
public import SerrePositivity.KST.NonConnective.DGSuspensionConnectedComparison

/-!
概要：完備化前の同じ実 fibration を反復し、同じ固定 K の非連結化候補へ渡す。
方針：各段の実構造辺を既存の native loop 列と元の実 Sp 余極限へ代入する。
規約：段別 I、実 fibration 辺、その非負次数比較、共終性に条件付き。
使われ方：K-7 c5・d3。全入力自然性と無条件の連結版 fibration は別工程。
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
local instance nativeFibrationSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
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

/-- 概要：段別実 fibration 辺に条件付きで、元の各反復入力の固定 K 間の構造辺。
方針：同じ段の同じ I を元の実構造辺構成へ代入する。
規約：始点・終点は既存の反復と固定 K のまま。
使われ方：同じ native loop 列への採用経路の代入。 -/
def dgSuspensionNativeFibrationStructureEdge (n : ℕ) :
    Sp.{max (u + 1) v}.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      ((OmegaSpectrum.nativeLoop.{max (u + 1) v}).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))) :=
  dgKappaNativeStructureEdge R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (ρ n)

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
  (hρ : ∀ (n : ℕ) (j : ℤ), 0 ≤ j → Function.Bijective
    (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk (ρ n).toTruncated) j))

include hcofinal hρ in
/-- 概要：実 fibration の非負次数比較と共終性に条件付きで、実隣接射は移動後の非負範囲で π 同型。
方針：同じ構造辺の非負次数比較を既存の自然な loop 次数移動へ渡す。
規約：全段の Sp 引き戻し性や零次全射性を要求しない。
使われ方：K-7 d3 の同じ実逐次列の安定化。 -/
theorem dgSuspensionNativeFibrationTransition_bijective (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j + n) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A
      (dgSuspensionNativeFibrationStructureEdge R s A ρ) n) j) := by
  apply (dgSuspensionNativeSequenceMap_bijective_iff_structure R s A _ n j).mpr
  rw [SpectrumHo.piMap_edge]
  change Function.Bijective (OmegaSpectrum.homotopyMap
    (dgKappaNativeStructureMap R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone (ρ n)) (j + n))
  exact dgKappaNativeStructureMap_nonnegative R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (ρ n) hcofinal (hρ n) (j + n) hj

include hcofinal hρ in
/-- 概要：同じ実 fibration と共終性に条件付きで、元の連結 K から実候補への比較は非負次数 π 同型。
方針：同じ実隣接射の安定化を元の実 Sp 余錐の零段の脚へ渡す。
規約：未供給の命題と段入力の存在は主張しない。全入力自然性は別工程。
使われ方：K-7 d3 の採用経路の連結比較。 -/
theorem dgSuspensionNativeFibrationConnectedComparison_bijective (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionConnectedComparison R s A (dgSuspensionNativeFibrationStructureEdge R s A ρ)) j) := by
  apply dgSuspensionConnectedComparison_bijective
  intro n
  exact dgSuspensionNativeFibrationTransition_bijective R s A ρ hcofinal hρ n j (by omega)

end SerrePositivity.KST.NonConnective
