module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces

/-!
概要：終対象は点からの実右随伴を与え、点からの実右随伴の値は終対象になる。
方針：点への相対終点境界充填と、随伴の元の pinched 写像空間同値を使う。
規約：写像空間の可縮性まで回収。使われ方：局所化の終対象保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma point_terminalBoundary {X : SSet.{u}} (p : X ⟶ (Δ[0] : SSet.{u}))
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x := by
  intro n a b ha _
  obtain ⟨l, hl⟩ := hx n a ha
  exact ⟨l, hl, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

def terminalPointAdjunction {X : SSet.{u}} [Quasicategory X]
    (p : X ⟶ (Δ[0] : SSet.{u})) (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction p (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) :=
  adjunctionOfRelativeTerminalSection (stdSimplex.isTerminalObj₀.hom_ext _ _) (by
    intro w
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact point_terminalBoundary p x hx)

lemma pointVertex_isTerminal (x : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  intro n b _
  exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

lemma pointAdjunction_isTerminal {X : SSet.{u}} [Quasicategory X]
    {F : (Δ[0] : SSet.{u}) ⟶ X} {p : X ⟶ (Δ[0] : SSet.{u})}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction p F) (w : (Δ[0] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌) w) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro y
  exact (a.pinchedHomEquivalence y w).isContractibleKan
    ((pointVertex_isTerminal w).pinchedHom_isContractibleKan _)

end SerrePositivity.KST.LocalizingInvariants
