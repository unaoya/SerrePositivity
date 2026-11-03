module

public import SerrePositivity.KST.LocalizingInvariants.AdjunctionOfOpposite
public import SerrePositivity.KST.LocalizingInvariants.AdjunctionCounitIso
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

omit [Quasicategory X] [Quasicategory Y] in
lemma oppositeSectionEquality (h : G ≫ F = 𝟙 Y) :
    SSet.opFunctor.map G ≫ SSet.opFunctor.map F = 𝟙 Y.op :=
  congrArg SSet.opFunctor.map h

omit [Quasicategory X] [Quasicategory Y] in
lemma oppositeSection_initialBoundary
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y))
    (y : Y.op _⦋0⦌) : InitialBoundaryLifting (SSet.opFunctor.map F)
      ((SSet.opFunctor.map G).app (Opposite.op ⦋0⦌) y) :=
  (hG (SSet.opObjEquiv y)).op_initial

def adjunctionOfRelativeTerminalSection (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) : QCatAdjunction F G :=
  adjunctionOfOpposite (adjunctionOfRelativeInitialSection (oppositeSectionEquality h)
    (oppositeSection_initialBoundary hG))

lemma fullyFaithful_of_relativeTerminalSection (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) : IsFullyFaithful G := by
  have hgf : IsFullyFaithful (G ≫ F) := h.symm ▸ isFullyFaithful_id Y
  intro x y
  have ht := pinchedHomMap_trivialKanFibration_of_terminalBoundaryLifting F (hG y)
    (G.app (Opposite.op ⦋0⦌) x)
  have hg := isQCatEquivalence_of_trivialKanFibration
    (pinchedHomMap F (G.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) y))
  have hc := (hgf x y).isQCatEquivalence
  rw [pinchedHomMap_comp] at hc
  exact (hg.cancel_right hc).isSimplicialHomotopyEquivalence

lemma relativeTerminalSection_counitHom_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counitHom := by
  let b := adjunctionOfRelativeInitialSection (oppositeSectionEquality h)
    (oppositeSection_initialBoundary hG)
  have : IsIso b.unitHom := by
    rw [adjunctionOfRelativeInitialSection_unit]
    infer_instance
  change IsIso (adjunctionOfOpposite b).counitHom
  rw [adjunctionOfOpposite_counit]
  infer_instance

lemma relativeTerminalSection_counit_isIso (h : G ≫ F = 𝟙 Y)
    (hG : ∀ y, TerminalBoundaryLifting F (G.app (Opposite.op ⦋0⦌) y)) :
    IsIso (adjunctionOfRelativeTerminalSection h hG).counit := by
  have := relativeTerminalSection_counitHom_isIso h hG
  exact counit_isIso_of_counitHom _

end SerrePositivity.KST.LocalizingInvariants
