module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanLeftHomInterval
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightFilling

/-!
概要：元の実精密化の二つの共通解像に、F1 の指定左右区間比較の自然性を適用する。
方針：同じ実共通終点の成分を二つの正方形に保持する。
規約：元の全 Hom、精密化、F1 の実二側円柱の指定同型を変更しない。
使われ方：元の指定精密化の左右区間作用を同じ全族の値へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (K L : KanObject.{u}) (e : (SimplicialCategory.sHom K L) _⦋1⦌)
local notation "H" => SimplicialCategory.sHom K L
local notation "FL" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseLeft H) ≫
  coherentKanLeftHomInterval K L
local notation "FR" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseRight H) ≫
  coherentKanRightHomInterval K L
local notation "T" => coherentKanTwoSidedIntervalIso K L

/-- 元の右解像の辺に対する、元の指定左右区間比較の同じ自然性正方形。 -/
lemma coherentKanRefinementRight_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FL).toTruncated) ≫
      (FunctorIso.app T (ULift.up (edgewiseRefinementVertex e))).hom =
    (FunctorIso.app T (ULift.up (edgewiseRefinementVertex
      (CategoryTheory.Functor.map H (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e)))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FR).toTruncated) :=
  edgewiseRefinementRight_naturality (coherentKanTwoSidedIntervalIso K L) e

/-- 元の左解像にも同じ指定比較を適用し、同じ実共通終点の成分を保持する。 -/
lemma coherentKanRefinementLeft_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FL).toTruncated) ≫
      (FunctorIso.app T (ULift.up (edgewiseRefinementVertex e))).hom =
    (FunctorIso.app T (ULift.up (edgewiseRefinementVertex
      (CategoryTheory.Functor.map H (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e)))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FR).toTruncated) :=
  edgewiseRefinementLeft_naturality (coherentKanTwoSidedIntervalIso K L) e

end SerrePositivity.InfinityCategories.F2
