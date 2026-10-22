module

public import SerrePositivity.InfinityCategories.F2.FunctorSquareTotalComponent
public import SerrePositivity.InfinityCategories.F2.CoherentColimitNativeUnitValueComparison

/-!
概要：元の単位正方形の全族の指定比較を、全空間上の同じ二面の相対比較へ戻す。
方針：native 標的への値の保持と恒等初期値での二面の回収を合成する。
規約：元の対角と全二面を保持。使われ方：a6 の指定作用比較との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "p" => leftUnstraighteningProjection F
local notation "x" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)

/-- 元の同じ下面の逆と上面から得る、native 標的への指定相対比較。 -/
def coherentColimitNativeUnitRelativeComparison :=
  (functorTriangleRelativeComparison (coherentColimitTargetLowerTriangle B H)).symm ≪≫
    functorTriangleRelativeComparison (coherentColimitNativeUnitFunctorTriangle B H)

/-- native 表示の全族の指定値は、同じ二面の元の相対比較合成と一致する。 -/
lemma coherentColimitNativeUnitValueComparison_total_heq :
    HEq (coherentColimitNativeUnitValueComparison B H p x)
      (coherentColimitNativeUnitRelativeComparison B H) :=
  functorSquareComparison_total_app_heq (coherentColimitNativeUnitFunctorTriangle B H)
    (coherentColimitTargetLowerTriangle B H)

/-- 元の標的・元の全族の指定値を、a6 と同じ標的の同じ二面の相対比較へ回収する。 -/
lemma coherentColimitUnitValueComparison_total_heq_nativeRelative :
    HEq (coherentColimitUnitValueComparison B H p x)
      (coherentColimitNativeUnitRelativeComparison B H) :=
  (coherentColimitUnitValueComparison_heq_native B H p x).trans
    (coherentColimitNativeUnitValueComparison_total_heq B H)

end SerrePositivity.InfinityCategories.F2
