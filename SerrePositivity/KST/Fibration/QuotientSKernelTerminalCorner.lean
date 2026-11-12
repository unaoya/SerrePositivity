module
public import SerrePositivity.KST.Fibration.QuotientSKernelEdges
public import SerrePositivity.KST.Fibration.KanTerminalComparison
public import SerrePositivity.KST.Fibration.RelativeSKernelDiagonalContraction

/-! # 元の商核 ∞ 四角形の同じ相対 S 核の角は終対象である -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の相対 S 核の収縮は、同じ全 coherent 商核四角形の同じ角の終対象性を与える。 -/
theorem quotientSKernelInfinitySquare_corner_isTerminal (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (quotientSKernelInfinitySquare i q) 0 1) := by
  rw [quotientSKernelInfinitySquare_corner]
  exact exInfinityVertex_isTerminal_of_localized_toPoint _
    (relativeSKernelDiagonal_toPoint_localized_isIso h)

end SerrePositivity.KST.Fibration
