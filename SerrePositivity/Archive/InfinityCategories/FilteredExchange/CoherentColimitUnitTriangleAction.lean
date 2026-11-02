module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTotalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquareConstantTargetValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerTriangleAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperTriangleAction

/-!
概要：元の単位正方形の二面の相対比較合成を、同じ二面の値への作用へ戻す。
方針：共有対角を持つ二面の比較の像の厳密な合成則を使う。
規約：元の全二面・対角・指定値を保持。使われ方：上下作用の共役因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "D" => coherentColimitTargetLowerTriangle B H
local notation "U" => coherentColimitNativeUnitFunctorTriangle B H
local notation "z" => coherentDiagramTotalVertex G

/-- 元の同じ下面の逆と上面から得る、元の値への全空間作用の指定比較。 -/
def coherentColimitUnitTriangleActionComparison :=
  (functorTriangleConstantTargetActionIso D).symm ≪≫ functorTriangleConstantTargetActionIso U

/-- 元の二面の相対比較合成の像は、同じ二面の全空間作用の比較合成と値まで一致する。 -/
lemma coherentColimitNativeUnitRelativeComparison_map_heq_action :
    HEq (VertexIso.map (coherentColimitNativeUnitRelativeComparison B H)
      ((constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
        (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom))
      (coherentColimitUnitTriangleActionComparison B H) :=
  functorSquareRelativeComparison_map_constantTarget U D

end SerrePositivity.InfinityCategories.F2
