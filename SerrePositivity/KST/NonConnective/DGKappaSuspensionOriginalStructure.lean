module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKernelKComparison

/-!
概要：元の Perf の固定 K からの実構造射の可逆性を、同じ相対 K 四角形へ戻す。
方針：指定 Perf 同値から得た実比較辺だけを消去し、元の核構造辺の判定を使う。
規約：明示相対屋根と指定全関手 Perf 同値に条件付き。K の局所化性や P との照合は未証明。
使われ方：K-7 c5 の実構造射と K-6 の実 fiber 判定の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance originalStructureSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance originalStructureHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (ρ : DGKappaSuspensionRelativeRoofInput R D I)
  (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
    (stableCategoryModel (dgKInputStableValue R ρ.kernel)))
  (Z : DGKappaZeroInput R D I)

/-- 明示屋根と指定 Perf 同値に条件付きで、元の構造辺の可逆性は同じ K 四角形の引き戻し性。 -/
theorem dgKappaSuspensionOriginalStructureMap_isInvertible_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionOriginalStructureMap R D I ρ e Z)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (ρ.diagram.square ≫ dgKInputK R) := by
  letI : IsIso (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionKernelKComparison R D I ρ e)).toTruncated) :=
    dgKappaSuspensionKernelKComparison_isInvertible R D I ρ e
  change IsIso (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionKernelKComparison R D I ρ e ≫
      ρ.nativeStructureBFMap R D I Z)).toTruncated) ↔ _
  rw [← Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgKappaSuspensionKernelKComparison R D I ρ e)
      (ρ.nativeStructureBFMap R D I Z)).toTruncated, isIso_comp_left_iff]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (ρ.nativeStructureBFMap_edge R D I Z)).trans
    (ρ.nativeStructureEdge_isInvertible_iff R D I Z)

end SerrePositivity.KST.NonConnective
