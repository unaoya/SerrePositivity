module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeTerminalAdjunction

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.AdjunctionOfOpposite
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.AdjunctionCounitIso
public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction
public import SerrePositivity.InfinityCategories.Core.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.Stable.TerminalMappingSpace

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

def adjunctionOfRelativeTerminalSection (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) : QCatAdjunction F G :=
  adjunctionOfOpposite (adjunctionOfRelativeInitialSection (oppositeSectionEquality h)
    (oppositeSection_initialBoundary hG))

lemma relativeTerminalSection_counitHom_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counitHom := by
  let b := adjunctionOfRelativeInitialSection (oppositeSectionEquality h)
    (oppositeSection_initialBoundary hG)
  have : IsIso b.unitHom := by
    rw [adjunctionOfRelativeInitialSection_unit]
    infer_instance
  change IsIso (adjunctionOfOpposite b).counitHom
  rw [_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.adjunctionOfOpposite_counit]
  infer_instance

lemma relativeTerminalSection_counit_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counit := by
  have := relativeTerminalSection_counitHom_isIso h hG
  exact counit_isIso_of_counitHom _

end SerrePositivity.KST.LocalizingInvariants
