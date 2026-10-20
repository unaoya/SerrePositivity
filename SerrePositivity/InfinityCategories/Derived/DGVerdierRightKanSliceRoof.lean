module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRightKanDiagram
public import SerrePositivity.InfinityCategories.Derived.RightKanSliceRoof
public import SerrePositivity.InfinityCategories.Derived.RoofEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondence
/-!
概要：実逆分母の右 Kan 比較の全 slice を、元の実 Verdier 屋根へ写す。
方針：同じ元の始域への射影で全錐を写し、標的の零単体を元の dg 対象へ厳密に戻す。
規約：商の射だけから屋根を再選択しない。使われ方：実屋根比較の slice との高次比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (hP : DGQuotient.localKFlat A D P) (x : D)
variable (R : DGVerdierRightKanDiagram A D P hP x)
variable (b : (rightKanShape (dgQuotientNerveProjection A D P)
  (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) _⦋0⦌)
/-- 右 Kan 形状の指定頂点の元の対象。 -/
def dgVerdierRightKanTarget : D :=
  (dgNerve.vertexEquiv A D) ((rightKanProjection (dgQuotientNerveProjection A D P)
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) b)
omit [IsDGPretriangulated A D] in
/-- 元の対象表示は、元の同じ零単体を厳密に復元する。 -/
lemma dgVerdierRightKanTarget_vertex :
    (rightKanProjection (dgQuotientNerveProjection A D P)
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) b =
        Simplex.vertex (dgVerdierRightKanTarget A D P x b) :=
  ((dgNerve.vertexEquiv A D).symm_apply_apply _).symm
/-- 実逆分母の右 Kan 比較に対する Quillen A の元の実 slice。 -/
abbrev dgVerdierRightKanCofinalSlice :=
  rightKanCofinalSlice (dgQuotientNerveProjection A D P)
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (dgVerdierRightKanMap A D P hP x R) b
/-- 右 Kan 比較の全 slice の実分母射影。 -/
abbrev dgVerdierRightKanCofinalSliceProjection :=
  rightKanCofinalSliceProjection (dgQuotientNerveProjection A D P)
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (dgVerdierRightKanMap A D P hP x R) b
/-- 右 Kan 比較の実 slice を、同じ分母・分子を持つ元の実屋根へ送る。 -/
def dgVerdierRightKanSliceRoofMap : dgVerdierRightKanCofinalSlice A D P hP x R b ⟶
    dgRoofCorrespondence A D P x (dgVerdierRightKanTarget A D P x b) :=
  rightKanCofinalSliceRoofMap (dgQuotientNerveProjection A D P)
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (dgVerdierOverSource A D P x) (dgVerdierRightKanMap A D P hP x R)
    (dgVerdierRightKanMap_projection A D P hP x R) b ≫
      (roofEndpointIso (dgVerdierOverSource A D P x)
        (dgVerdierRightKanTarget_vertex A D P x b)).hom
/-- 右 Kan 比較の全 slice の実屋根表示は、元の同じ実分母図式を厳密に保持する。 -/
lemma dgVerdierRightKanSliceRoofMap_projection :
    dgVerdierRightKanSliceRoofMap A D P hP x R b ≫
      dgRoofCorrespondenceProjection A D P x (dgVerdierRightKanTarget A D P x b) =
        dgVerdierRightKanCofinalSliceProjection A D P hP x R b := by
  dsimp only [dgVerdierRightKanSliceRoofMap, dgRoofCorrespondenceProjection]
  rw [Category.assoc, roofEndpointIso_snd, rightKanCofinalSliceRoofMap_projection]
end SerrePositivity.InfinityCategories
