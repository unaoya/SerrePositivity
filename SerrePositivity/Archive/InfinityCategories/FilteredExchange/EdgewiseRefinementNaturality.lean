module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSectionNaturality

/-!
概要：同じ元の精密化の二つの共通解像に対する指定比較の二自然性正方形。
方針：実始点と同じ実共通終点を持つ二辺へ、指定関手同型の自然性を適用する。
規約：指定比較の成分も二辺の実代表も変更しない。
使われ方：左右区間比較の共通終点成分を消去して元の精密化の作用を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X : SSet.{u}} {Y : SSet.{max u v}} [Quasicategory Y]
  [Quasicategory ((SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X))]
  {f g : (SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X) ⟶ Y}
  (η : FunctorIso f g) (e : X _⦋1⦌)

/-- 元の右精密化に対する指定比較の自然性は同じ実共通終点の成分を保持する。 -/
lemma edgewiseRefinementRight_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementRightEdgeUlift.{u, v} e).map f).toTruncated) ≫
      (η.app (ULift.up (edgewiseRefinementVertex e))).hom =
    (η.app (ULift.up (edgewiseRefinementVertex
      (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e)))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementRightEdgeUlift.{u, v} e).map g).toTruncated) :=
  functorIso_app_edge_naturality η (edgewiseRefinementRightEdgeUlift.{u, v} e)

/-- 元の左精密化にも同じ指定比較と同じ実共通終点の成分の自然性を適用する。 -/
lemma edgewiseRefinementLeft_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementLeftEdgeUlift.{u, v} e).map f).toTruncated) ≫
      (η.app (ULift.up (edgewiseRefinementVertex e))).hom =
    (η.app (ULift.up (edgewiseRefinementVertex
      (X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e)))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementLeftEdgeUlift.{u, v} e).map g).toTruncated) :=
  functorIso_app_edge_naturality η (edgewiseRefinementLeftEdgeUlift.{u, v} e)

end SerrePositivity.InfinityCategories.F2
