module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalArrowCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomRawInputIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.PullbackReindexIso
/-!
概要：正本の区間 Hom 引き戻しを同じ二合成対応と元左右 Hom 入力へ厳密に移す。
方針：元の底を保ち、矢印座標と入力座標の二同型を同時に前合成する。
規約：底の適合条件と両射影を保持し、まだ底の二作用の照合は結論しない。
使われ方：正本標的を既存の入力付き四座標模型と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingLaxHomIntervalCoordinates :=
  pullback
    ((dgGluingLaxHomIntervalArrowCoordinateIso R C D M X Y).inv ≫
      dgGluingLaxHomIntervalEndpointMap R C D M X Y)
    ((dgGluingLaxHomRawInputIso R C D M X Y).inv ≫
      dgGluingLaxHomIntervalInputBase R C D M X Y)

def dgGluingLaxHomIntervalCoordinatesIso :
    dgGluingLaxHomIntervalPullback R C D M X Y ≅
      dgGluingLaxHomIntervalCoordinates R C D M X Y :=
  dgGluingPullbackReindexIso (dgGluingLaxHomIntervalEndpointMap R C D M X Y)
    (dgGluingLaxHomIntervalInputBase R C D M X Y)
    (dgGluingLaxHomIntervalArrowCoordinateIso R C D M X Y)
    (dgGluingLaxHomRawInputIso R C D M X Y)

lemma dgGluingLaxHomIntervalCoordinatesIso_arrow :
    (dgGluingLaxHomIntervalCoordinatesIso R C D M X Y).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (dgGluingLaxHomIntervalArrowCoordinateIso R C D M X Y).hom :=
  dgGluingPullbackReindexIso_first _ _ _ _

lemma dgGluingLaxHomIntervalCoordinatesIso_inputs :
    (dgGluingLaxHomIntervalCoordinatesIso R C D M X Y).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (dgGluingLaxHomRawInputIso R C D M X Y).hom :=
  dgGluingPullbackReindexIso_second _ _ _ _
end SerrePositivity.InfinityCategories
