module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentConstantTriangleLargeRecovery

/-!
概要：a6 への既存の上面作用比較を、元の全上面の大きい比較に値まで同定する。
方針：三角形表現の縮小・復元の回収式を適用し、元の native 作用の比較を保持する。
規約：上面・対角・単位の指定表現を保持。使われ方：二面比較の指定共役因子の消去。
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

/-- 既存の上面作用比較は、元の上面比較と同じ native 作用比較の逆との合成。 -/
lemma coherentColimitUpperActionIso_eq_triangle
    (hn : coherentLargeTotalUnit F ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentTotalVertexMap F G
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) =
        (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
            coherentDiagramTotalUnit G)) :
    coherentColimitUpperActionIso B H =
      coherentConstantTriangleLargeComparison F G (coherentDiagramTotalVertex G)
        (coherentDiagramTotalUnit G) (coherentNativeUnitRepresentation G)
        (coherentVertexOfHomotopy H) (coherentColimitNativeUnitTriangle B H) ≪≫
          (functorIsoOfEq (coherentTotalMapNativeActionIso F G
            (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) rfl hn).symm := by
  unfold coherentColimitUpperActionIso
  simp only [coherentColimitNativeDiagonalRepresentation,
    coherentConstantTriangleRepresentation_largeIso_eq]
  congr 1

end SerrePositivity.InfinityCategories.F2
