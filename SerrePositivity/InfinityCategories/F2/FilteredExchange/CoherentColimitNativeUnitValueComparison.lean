module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorSquareTargetTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitComparisonTarget
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitValueComparison

/-!
概要：元の単位正方形の二面の比較合成を、元の native 標的表示に戻す。
方針：同じ三円柱と二実面を保つ標的等式の輸送を適用する。
規約：元の指定対角と合成の値を保持。使われ方：a6 の全空間作用との指定値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {C : SSet.{u + 1}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
  (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
  (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌)

/-- 同じ全二面から得る、native 標的表示での元の指定比較。 -/
def coherentColimitNativeUnitValueComparison :=
  ((functorTriangleSequentialPostComparison (coherentColimitTargetLowerTriangle B H) p).app
    x).symm ≪≫
      (functorTriangleSequentialPostComparison (coherentColimitNativeUnitFunctorTriangle B H)
        p).app x

/-- 元の二面の指定比較の合成は、native 標的表示の同じ合成と値まで一致する。 -/
lemma coherentColimitUnitValueComparison_heq_native :
    HEq (coherentColimitUnitValueComparison B H p x)
      (coherentColimitNativeUnitValueComparison B H p x) :=
  functorSquareComparison_app_heq_target
    (coherentColimitUnitUpperTriangle B H) (coherentColimitUnitLowerTriangle B H)
    (coherentColimitNativeUnitFunctorTriangle B H) (coherentColimitTargetLowerTriangle B H)
    (congrArg SSet.const (coherentDiagramTotalCocone_vertex G))
    (coherentNativeUnitHomotopy_h G).symm rfl rfl rfl rfl p x

end SerrePositivity.InfinityCategories.F2
