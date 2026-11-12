module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComparisonReturnHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.ContractibleHomotopyRetract

/-!
概要：各点の標準単位比較の同値性から comma の指定単位の始対象性を導く。
方針：導来 fiber の可縮性を、戻る合成の実際のホモトピーで写像空間へ移す。
規約：指定単位 η の誘導する比較を使い、任意の各点の同値の選択では代用しない。
使われ方：B1 の Cor 6.2.6.5 の逆方向で普遍矢印性を得る中間段階。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：単位比較の同値条件の下で、指定単位から出る comma 写像空間は可縮。
方針：可縮な導来 fiber への比較と、恒等射から戻る合成へのホモトピーを使う。
規約：比較の両方向の射の存在だけではなく、証明済みの戻る合成を用いる。
使われ方：comma の指定頂点の始対象性の写像空間判定。 -/
lemma UnitMappingSpaceCondition.unitCommaMappingSpace_isContractibleKan
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w) := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber_comp_return_homotopy η x w
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isContractibleKan_of_homotopy_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaMappingToComparisonFiber η x w)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComparisonFiberToCommaMapping η x w) H
    (hη.unitIntervalComparisonFiber_isContractibleKan x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowVertex G x w))

/-- 概要：各点の標準単位比較の同値性から、指定単位の comma 始対象条件が従う。
方針：出る区間写像空間の可縮性を始対象性の判定へ渡す。
規約：余単位・三角恒等式の構成は後続の工程。
使われ方：局所的な単位の普遍矢印性から随伴を構成する接続点。 -/
lemma UnitMappingSpaceCondition.unitCommaInitialCondition
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} {η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)}
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaInitialCondition η :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaInitialCondition_iff_intervalMappingSpaces η).mpr
    hη.unitCommaMappingSpace_isContractibleKan

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
