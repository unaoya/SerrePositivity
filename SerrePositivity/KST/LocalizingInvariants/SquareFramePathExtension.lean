module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFramePathExtension

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SquareFrameFunctoriality
public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：元の正方形の境界に指定された四辺の可逆 path を、正方形全体へ延長する。
方針：path の始点評価の自明 Kan 性と境界の単射性を使う。
規約：指定した境界 path は厳密に保持。使われ方：元の BF 合成射への四辺の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrame
variable {X : SSet.{u}} [Quasicategory X] (f : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareFrame (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X))
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (hf : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.postcomp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare Q)

namespace PathExtension
variable {f Q} (w : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.PathExtension f Q)

def comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Q w.target :=
  (eqToIso (congrArg (fun g => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) w.source)).symm ≪≫
    equivalencePathFamilyIso w.family

lemma target_isPullback (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare w.target :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPullbackSquare.of_functorIso hQ (_root_.SerrePositivity.KST.LocalizingInvariants.SquareFrame.PathExtension.comparison w)

end PathExtension
end SerrePositivity.KST.LocalizingInvariants.SquareFrame
