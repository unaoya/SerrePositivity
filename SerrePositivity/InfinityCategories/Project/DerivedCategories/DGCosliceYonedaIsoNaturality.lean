module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationCartesianRestriction
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
/-- 底の同型に沿う同じ coslice の分類図式の全関手比較。 -/
def dgCosliceYonedaSpaceIsoNaturality (e : X ≅ Y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity X x)
      ((SSet.uliftFunctor.{u + 1, u}).map e.hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaSpaceInfinity Y (e.hom.app _ x)) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso e x
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso_projection e x
  have hs : U.map d.hom ≫ U.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (e.hom.app _ x))) =
    U.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) ≫ U.map e.hom := by
    rw [← Functor.map_comp, hd, Functor.map_comp]
  have hi : IsIso (U.map d.hom) := inferInstanceAs (IsIso (U.mapIso d).hom)
  have hg : IsIso (U.map e.hom) := inferInstanceAs (IsIso (U.mapIso e).hom)
  let hsq := IsPullback.of_horiz_isIso (CommSq.mk hs)
  let R := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation Y (e.hom.app _ x)).cartesianRestrict
    (U.map d.hom) (U.map e.hom) hsq
  have (n : SimplexCategoryᵒᵖ) : Small.{u}
      ((U.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1}
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)).obj n)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallTransportRepresentationDiagramIso _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCosliceYonedaTransportRepresentation X x) R
end SerrePositivity.InfinityCategories.Project.DerivedCategories
