module
public import SerrePositivity.KST.SConstruction.DoubleCofiberGrid
public import SerrePositivity.KST.SConstruction.ArrowSquareComparison
public import SerrePositivity.KST.SConstruction.CofiberFamilyVanishingIsos

/-! # 二重 cofiber 格子の二つの入力辺の同型
概要：左下の二つの比較が零 cofiber を持つとき、格子の上辺と右辺の族が coherent に同型。
方針：族を関手圏に転置し、指定された下辺の可逆性を三角形 prism に渡す。
規約：族全体の関手同型を構成する。使われ方：相対切断の中央評価の逆同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- cofiber 族の入力辺の転置は、その族を関手圏の四角形にした下辺。 -/
lemma cofiberFamilyTriangle_input {E C : SSet.{u}} (H : E ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (cofiberFamilyTriangle H).square =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C (H ≫ cofiberProjection C) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
    (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)).symm

/-- cofiber 族の商が全点で零なら、関手圏内の指定された入力辺そのものが可逆。 -/
lemma cofiberFamilyInput_edge_isInvertible {E C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (H : E ⟶ cofiberDiagrams C)
    (hz : ∀ e : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((H ≫ cofiberApex C).app (Opposite.op ⦋0⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C (H ≫ cofiberProjection C)))) := by
  have hq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (cofiberFamilyTriangle H).square 1 1) := by
    rw [cofiberFamilyTriangle_apex]
    exact isZeroVertex_functorVertex_of_pointwise _ hz
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (cofiberFamilyTriangle H).square) :=
    (cofiberFamilyTriangle H).isIso_f_of_zero_cofiber (cofiberFamilyTriangle_isCofiber H) hq
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge _).trans
    (congrArg SSet.yonedaEquiv (cofiberFamilyTriangle_input H)))).mp hi

/-- 二重 cofiber 格子の下辺は元の零番目の行の入力の転置。 -/
lemma doubleCofiberGrid_bottom {E C : SSet.{u}}
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (doubleCofiberGrid J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C
        (doubleCofiberRow J 0 ≫ cofiberProjection C) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C) (doubleCofiberGrid_row J 0)

/-- 二重 cofiber 格子の左辺は元の零番目の列の入力の転置。 -/
lemma doubleCofiberGrid_left {E C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (doubleCofiberGrid J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C
        (doubleCofiberColumn J 0 ≫ cofiberProjection C) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C) (doubleCofiberGrid_column J 0)

/-- 二重 cofiber 格子の上辺は元の一番目の行の入力の転置。 -/
lemma doubleCofiberGrid_top {E C : SSet.{u}}
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (doubleCofiberGrid J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C
        (doubleCofiberRow J 1 ≫ cofiberProjection C) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C) (doubleCofiberGrid_row J 1)

/-- 二重 cofiber 格子の右辺は元の一番目の列の入力の転置。 -/
lemma doubleCofiberGrid_right {E C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] ⊗ Δ[1] : SSet.{u}) C
        (doubleCofiberGrid J) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C
        (doubleCofiberColumn J 1 ≫ cofiberProjection C) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv E (Δ[1] : SSet.{u}) C) (doubleCofiberGrid_column J 1)

end SerrePositivity.KST.SConstruction
