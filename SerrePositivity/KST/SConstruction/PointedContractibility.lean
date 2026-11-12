module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.KST.Spectra.AcyclicFibrationLifting

/-! # 弱可縮な点つき Kan 複体の境界充填
概要：局所化で一点と同値な点つき Kan 複体は全境界を充填する。
方針：実際の π 同型へ移し、点への Kan fibration の Whitehead の充填を使う。
規約：標準三公理のみ。使われ方：点つき経路の Kan 模型の可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 概要：弱可縮な点つき Kan 複体は実際に全境界を充填する可縮 Kan 複体。
方針：点への射の π 同型と Kan fibration 性から全単射 RLP を得る。
規約：非空性は指定した基点から得る。使われ方：点つき経路全空間の可縮 Kan 性。 -/
lemma pointedIsContractibleKan_of_localized_toPoint (Z : PointedSimplicialSet.{u})
    [KanComplex Z.right]
    (hZ : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit Z.right))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan Z.right := by
  let e : terminal SSet.{u} ≅ 𝟙_ SSet.{u} :=
    terminalIsTerminal.uniqueUpToIso isTerminalTensorUnit
  let : KanComplex (𝟙_ SSet.{u}) := by
    change Fibration (terminal.from (𝟙_ SSet.{u}))
    have ht : terminal.from (𝟙_ SSet.{u}) = e.inv := terminal.hom_ext _ _
    rw [ht]
    infer_instance
  have he : toUnit Z.right = terminal.from Z.right ≫ e.hom := isTerminalTensorUnit.hom_ext _ _
  let : Fibration (toUnit Z.right) := by
    rw [he]
    infer_instance
  have hp := kanPiIsomorphism_of_localized_isIso (toUnit Z.right) hZ
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism (toUnit Z.right) hp Z.basepoint
  intro n a
  let : HasLiftingProperty (boundary n).ι (toUnit Z.right) := hr (boundary n).ι inferInstance
  let sq : CommSq a (boundary n).ι (toUnit Z.right) (toUnit (Δ[n] : SSet.{u})) :=
    ⟨isTerminalTensorUnit.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
