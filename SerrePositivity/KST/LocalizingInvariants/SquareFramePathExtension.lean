module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFramePathExtension

public import SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrameFunctoriality
public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

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
namespace SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame
variable {X : SSet.{u}} [Quasicategory X] (f : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame (equivalencePath X))
  (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
  (hf : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.postcomp f) (equivalencePathEndpoint X 0) = _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare Q)

namespace PathExtension
variable {f Q} (w : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension f Q)

def comparison : FunctorIso Q w.target :=
  (eqToIso (congrArg (fun g => HomotopyCategory.mk (functorVertex g)) w.source)).symm ≪≫
    equivalencePathFamilyIso w.family

lemma target_isPullback (hQ : IsPullbackSquare Q) : IsPullbackSquare w.target :=
  IsPullbackSquare.of_functorIso hQ w.comparison

end PathExtension
end SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame
