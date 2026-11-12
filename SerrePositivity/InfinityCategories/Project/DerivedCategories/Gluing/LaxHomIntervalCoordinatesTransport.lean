module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomIntervalCoordinatesIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIsoPrecomposition
/-!
概要：正本 lax Hom 標的を元の二入力と二合成対応を保つ区間座標へ同値に移す。
方針：pinched・区間比較へ両座標の厳密同型を後合成する。
規約：元の正本比較・全矢印座標・入力側第二射影を保持する。
使われ方：底の導来二作用を照合し、既存の四座標比較の逆射を主比較へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingLaxHomIntervalCoordinatesTransport :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPinchedIntervalTransport R C D M X Y ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesIso R C D M X Y).hom

lemma dgGluingLaxHomIntervalCoordinatesTransport_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyEquivalence_postcomp_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPinchedIntervalTransport R C D M X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesIso R C D M X Y)).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPinchedIntervalTransport_equivalence R C D M X Y)

lemma dgGluingLaxHomIntervalCoordinatesTransport_arrow :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫
      dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomArrowCompositionComparison R C D M X Y := by
  rw [dgGluingLaxHomIntervalCoordinatesTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesIso_arrow]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalArrowCoordinateIso_comparison R C D M X Y

lemma dgGluingLaxHomIntervalCoordinatesTransport_inputs :
    dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomRawInputIso R C D M X Y).hom := by
  rw [dgGluingLaxHomIntervalCoordinatesTransport, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesIso_inputs,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPinchedIntervalTransport_inputs]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
