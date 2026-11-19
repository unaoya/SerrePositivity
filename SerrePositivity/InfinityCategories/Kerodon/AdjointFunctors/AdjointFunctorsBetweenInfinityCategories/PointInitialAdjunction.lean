module

public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IntervalMappingContractible

/-!
概要：始対象は点からの実左随伴を与え、点からの実左随伴の値は始対象になる。
方針：点への相対境界充填と、随伴の実写像空間同値の双方を使う。
規約：単なるホモトピー圏の随伴へ弱めない。使われ方：局所化の始対象保存。
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

lemma point_initialBoundary {X : SSet.{u}} (p : X ⟶ (Δ[0] : SSet.{u}))
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x := by
  intro n a b ha _
  obtain ⟨l, hl⟩ := hx n a ha
  exact ⟨l, hl, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

def initialPointAdjunction {X : SSet.{u}} [Quasicategory X]
    (p : X ⟶ (Δ[0] : SSet.{u})) (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) p :=
  adjunctionOfRelativeInitialSection (stdSimplex.isTerminalObj₀.hom_ext _ _) (by
    intro w
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact point_initialBoundary p x hx)

lemma pointVertex_isInitial (x : (Δ[0] : SSet.{u}) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  intro n b _
  exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩

lemma pointAdjunction_isInitial {X : SSet.{u}} [Quasicategory X]
    {F : (Δ[0] : SSet.{u}) ⟶ X} {p : X ⟶ (Δ[0] : SSet.{u})}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F p) (w : (Δ[0] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (F.app (Opposite.op ⦋0⦌) w) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_intervalMappingSpace_isContractibleKan
  intro y
  exact (a.intervalMappingEquivalence w y).symm.isContractibleKan
    ((pointVertex_isInitial w).intervalMappingSpace_isContractibleKan _)

end SerrePositivity.KST.LocalizingInvariants
