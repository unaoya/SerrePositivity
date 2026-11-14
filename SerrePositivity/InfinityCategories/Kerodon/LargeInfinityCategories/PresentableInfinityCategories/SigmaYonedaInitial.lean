module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace

/-!
概要：元の Yoneda 前層は、始対象を元の一点空間と同値な終対象へ送る。
方針：元の表現可能前層の値比較に、始対象からの元の写像空間の可縮性を移す。
規約：別の Hom 前層を選ばず、元の representablePresheafInfinity の値を使う。
使われ方：P_Σ への Yoneda 因子化の空積の場合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 始対象での元の Yoneda 前層の Kan 値は可縮。 -/
lemma representablePresheafInfinity_initialValue_isContractibleKan
    {C : SSet.{u}} [Quasicategory C] {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app
      (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x)))).obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence x y).symm.isContractibleKan
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftRightEquivalence x y).isContractibleKan
      (hx.pinchedHomLeft_isContractibleKan y))

/-- 元の Yoneda 前層は始対象を空間の ∞ 圏の終対象へ送る。 -/
lemma representablePresheafInfinity_initialValue_isTerminal
    {C : SSet.{u}} [Quasicategory C] {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm x))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
    (representablePresheafInfinity_initialValue_isContractibleKan hx y)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
