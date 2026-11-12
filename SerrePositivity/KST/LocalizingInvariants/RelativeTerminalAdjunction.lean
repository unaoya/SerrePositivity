module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeTerminalAdjunction

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionOfOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.AdjunctionCounitIso
public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalMappingSpace

/-!
概要：相対終点境界を充填する切断は、元の射影の充満忠実な右随伴になる。
方針：反転側の相対始点判定で実随伴を作り、二胞体の反転全単射で戻す。
規約：始域と標的の元の関手を保持する。使われ方：K-8 の C 包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

def adjunctionOfRelativeTerminalSection (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfOpposite (adjunctionOfRelativeInitialSection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.oppositeSectionEquality h)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.oppositeSection_initialBoundary hG))

lemma relativeTerminalSection_counitHom_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counitHom := by
  let b := adjunctionOfRelativeInitialSection (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.oppositeSectionEquality h)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.oppositeSection_initialBoundary hG)
  have : IsIso b.unitHom := by
    rw [adjunctionOfRelativeInitialSection_unit]
    infer_instance
  change IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfOpposite b).counitHom
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.adjunctionOfOpposite_counit]
  infer_instance

lemma relativeTerminalSection_counit_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counit := by
  have := relativeTerminalSection_counitHom_isIso h hG
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.counit_isIso_of_counitHom _

end SerrePositivity.KST.LocalizingInvariants
