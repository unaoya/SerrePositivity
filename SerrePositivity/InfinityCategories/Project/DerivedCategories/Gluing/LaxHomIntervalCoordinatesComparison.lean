module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomIntervalCoordinatesTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomRawInputComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomInputCoordinateComparison
/-!
概要：正本標的の区間座標と入力付き四座標比較が同じ矢印と元二入力を持つことを示す。
方針：二つの実輸送の射影則へ元左右 Hom 鎖射影の厳密一致を代入する。
規約：二つの底の適合条件の同一視はここで仮定しない。
使われ方：底の二作用を照合した後、正本比較の同値性と実逆射を戻す。
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
lemma dgGluingLaxHomIntervalCoordinatesComparison_arrow :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.fst _ _ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison R C D M X Y ≫ pullback.fst _ _ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesTransport_arrow,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison_arrow]
lemma dgGluingLaxHomIntervalCoordinatesComparison_inputs :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.snd _ _ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison R C D M X Y ≫ pullback.snd _ _ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesTransport_inputs,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison_raw_inputs,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison_inputs]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
