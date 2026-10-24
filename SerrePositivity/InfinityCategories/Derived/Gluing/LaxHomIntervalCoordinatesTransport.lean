module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomIntervalCoordinatesIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingLaxHomIntervalCoordinatesTransport :=
  dgGluingLaxHomPinchedIntervalTransport R C D M X Y ≫
    (dgGluingLaxHomIntervalCoordinatesIso R C D M X Y).hom

lemma dgGluingLaxHomIntervalCoordinatesTransport_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff
    (dgGluingLaxHomPinchedIntervalTransport R C D M X Y)
    (dgGluingLaxHomIntervalCoordinatesIso R C D M X Y)).mpr
      (dgGluingLaxHomPinchedIntervalTransport_equivalence R C D M X Y)

lemma dgGluingLaxHomIntervalCoordinatesTransport_arrow :
    dgGluingLaxHomPullbackComparison R C D M X Y ≫
      dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y := by
  rw [dgGluingLaxHomIntervalCoordinatesTransport, Category.assoc,
    dgGluingLaxHomIntervalCoordinatesIso_arrow]
  exact dgGluingLaxHomIntervalArrowCoordinateIso_comparison R C D M X Y

lemma dgGluingLaxHomIntervalCoordinatesTransport_inputs :
    dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (dgGluingLaxHomRawInputIso R C D M X Y).hom := by
  rw [dgGluingLaxHomIntervalCoordinatesTransport, Category.assoc,
    dgGluingLaxHomIntervalCoordinatesIso_inputs,
    reassoc_of% dgGluingLaxHomPinchedIntervalTransport_inputs]
end SerrePositivity.InfinityCategories
