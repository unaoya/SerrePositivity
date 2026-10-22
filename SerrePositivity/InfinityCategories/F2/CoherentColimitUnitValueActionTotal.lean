module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitValueAction
public import SerrePositivity.InfinityCategories.F2.FunctorSquareTotalComponentMap
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitActionConjugacy

/-!
概要：元の標的余錐の値へ写した二面比較を、a6 へ接続する同じ native な中央比較へ戻す。
方針：標的等式と全空間成分の元の指定値を保ち、同じ相対二面比較の像を回収する。
規約：元の二面・対角を保持。使われ方：三角形整合式の三辺の値を a6 と照合する。
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
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)

/-- 元の値への全空間での比較は、a6 の指定共役式の同じ中央比較と値まで一致する。 -/
lemma coherentColimitUnitValueAction_total_heq_native :
    HEq (coherentColimitUnitValueAction B H p x₀)
      (coherentColimitNativeTriangleActionComparison B H) := by
  refine (coherentColimitUnitValueAction_heq_native B H p x₀).trans ?_
  refine (functorSquareComparison_total_app_map_heq
    (coherentColimitNativeUnitFunctorTriangle B H) (coherentColimitTargetLowerTriangle B H)
    ((constantUnstraighteningRelativeIso p (coherentDiagramTotalVertex G)).hom ≫
      (ihom (leftUnstraightening F)).map
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)).trans ?_
  exact (coherentColimitNativeUnitRelativeComparison_map_heq_action B H).trans
    (coherentColimitNativeTriangleActionComparison_heq_original B H).symm

end SerrePositivity.InfinityCategories.F2
