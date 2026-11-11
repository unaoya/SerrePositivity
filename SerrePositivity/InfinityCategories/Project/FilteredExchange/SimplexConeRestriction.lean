module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport

/-!
概要：標準単体上の元の錐の極限性は最初の頂点への制限で判定できる。
方針：left anodyne な形状制限による slice の自明 Kan 性で終対象性を移す。
規約：元の錐と頂点を保持。使われ方：coherent filtered 極限交換の単体の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- left anodyne な制限は、元の指定錐の極限性を保存・反映する。 -/
lemma isLimitCone_restrict_iff_of_leftAnodyne {J K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (f : J ⟶ K) [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration p f hf
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f)).isTerminalVertex_iff c).symm

/-- 標準単体の最初の頂点の包含は単射。 -/
lemma stdSimplex_firstVertex_mono (n : ℕ) : Mono (SSet.yonedaEquiv.symm
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) := by
  suffices ∀ d, Mono ((SSet.yonedaEquiv.symm
        (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) :
          (Δ[0] : SSet.{u}) ⟶ Δ[n]).app d) from NatTrans.mono_of_mono_app _
  intro d
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  apply stdSimplex.ext
  intro j
  apply Fin.ext
  omega

/-- 単体の最初の頂点への制限は、元の錐そのものの極限性を判定する。 -/
lemma isLimitCone_stdSimplex_iff_firstVertex {X : SSet.{u}} [Quasicategory X]
    {n : ℕ} {p : (Δ[n] : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (SSet.yonedaEquiv.symm
      (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) := by
  have := stdSimplex_firstVertex_mono.{u} n
  exact (isLimitCone_restrict_iff_of_leftAnodyne c _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stdSimplex_firstVertex_leftAnodyne n)).symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
