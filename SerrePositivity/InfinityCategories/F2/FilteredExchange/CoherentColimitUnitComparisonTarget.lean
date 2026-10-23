module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleTargetTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitLowerTriangle

/-!
概要：元の単位正方形の上下二面の指定比較を、a6 と同じ標的へ値を保って移す。
方針：元の余極限頂点の等式と、変更されない全円柱・全二単体を使う。
規約：対角と二面を再選択しない。使われ方：元の単位比較と native 作用比較の照合。
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

/-- 元の上面の各指定値は、native 頂点表示の同じ上面の指定値に一致する。 -/
lemma coherentColimitUnitUpperComparison_app_heq_native :
    HEq ((functorTriangleSequentialPostComparison
      (coherentColimitUnitUpperTriangle B H) p).app x)
      ((functorTriangleSequentialPostComparison
        (coherentColimitNativeUnitFunctorTriangle B H) p).app x) :=
  functorTriangleSequentialPostComparison_app_heq_target _ _
    (congrArg SSet.const (coherentDiagramTotalCocone_vertex G))
    (coherentNativeUnitHomotopy_h G).symm rfl rfl p x

/-- 元の下面の各指定値は、a6 の元の標的表示の同じ下面の指定値に一致する。 -/
lemma coherentColimitUnitLowerComparison_app_heq_target :
    HEq ((functorTriangleSequentialPostComparison
      (coherentColimitUnitLowerTriangle B H) p).app x)
      ((functorTriangleSequentialPostComparison
        (coherentColimitTargetLowerTriangle B H) p).app x) :=
  functorTriangleSequentialPostComparison_app_heq_target _ _
    (congrArg SSet.const (coherentDiagramTotalCocone_vertex G)) rfl rfl rfl p x

end SerrePositivity.InfinityCategories.F2
