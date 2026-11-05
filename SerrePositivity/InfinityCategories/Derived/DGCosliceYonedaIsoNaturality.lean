module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.F1.Transport.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationCartesianRestriction
/-!
概要：coslice の Yoneda 評価を、底の同型による元の全関手の前合成へ比較する。
方針：同じ coslice 同型の引戻し四角形に沿って transport 表現を制限する。
規約：全関手族を同じ可縮な表現空間で比較する。使われ方：dg 反対 nerve の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
/-- 底の同型に沿う同じ coslice の分類図式の全関手比較。 -/
def dgCosliceYonedaSpaceIsoNaturality (e : X ≅ Y) (x : X _⦋0⦌) :
    FunctorIso (dgCosliceYonedaSpaceInfinity X x)
      ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫
        dgCosliceYonedaSpaceInfinity Y (e.hom.app _ x)) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let d := pointCoslicePostIso e x
  have hd := pointCoslicePostIso_projection e x
  have hs : U.map d.hom ≫ U.map
      (sliceUnderProjection (SSet.yonedaEquiv.symm (e.hom.app _ x))) =
    U.map (sliceUnderProjection (SSet.yonedaEquiv.symm x)) ≫ U.map e.hom := by
    rw [← Functor.map_comp, hd, Functor.map_comp]
  have hi : IsIso (U.map d.hom) := inferInstanceAs (IsIso (U.mapIso d).hom)
  have hg : IsIso (U.map e.hom) := inferInstanceAs (IsIso (U.mapIso e).hom)
  let hsq := IsPullback.of_horiz_isIso (CommSq.mk hs)
  let R := (dgCosliceYonedaTransportRepresentation Y (e.hom.app _ x)).cartesianRestrict
    (U.map d.hom) (U.map e.hom) hsq
  have (n : SimplexCategoryᵒᵖ) : Small.{u}
      ((U.obj (sliceUnder (SSet.yonedaEquiv.symm x))).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1}
      ((sliceUnder (SSet.yonedaEquiv.symm x)).obj n)))
  exact smallTransportRepresentationDiagramIso _
    (dgCosliceYonedaTransportRepresentation X x) R
end SerrePositivity.InfinityCategories
