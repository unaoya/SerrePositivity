module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRightKanDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RightKanSliceRoof
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofEndpointTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGRoofCorrespondence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x : D)
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRightKanDiagram A D P hP x)
variable (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))) _⦋0⦌)
/-- 右 Kan 形状の指定頂点の元の対象。 -/
def dgVerdierRightKanTarget : D :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) b)
omit [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] in
/-- 元の対象表示は、元の同じ零単体を厳密に復元する。 -/
lemma dgVerdierRightKanTarget_vertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))).app (Opposite.op ⦋0⦌) b =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgVerdierRightKanTarget A D P x b) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D).symm_apply_apply _).symm
/-- 実逆分母の右 Kan 比較に対する Quillen A の元の実 slice。 -/
abbrev dgVerdierRightKanCofinalSlice :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightKanCofinalSlice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R) b
/-- 右 Kan 比較の全 slice の実分母射影。 -/
abbrev dgVerdierRightKanCofinalSliceProjection :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightKanCofinalSliceProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R) b
/-- 右 Kan 比較の実 slice を、同じ分母・分子を持つ元の実屋根へ送る。 -/
def dgVerdierRightKanSliceRoofMap : dgVerdierRightKanCofinalSlice A D P hP x R b ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x (dgVerdierRightKanTarget A D P x b) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightKanCofinalSliceRoofMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap A D P hP x R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierRightKanMap_projection A D P hP x R) b ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x)
        (dgVerdierRightKanTarget_vertex A D P x b)).hom
/-- 右 Kan 比較の全 slice の実屋根表示は、元の同じ実分母図式を厳密に保持する。 -/
lemma dgVerdierRightKanSliceRoofMap_projection :
    dgVerdierRightKanSliceRoofMap A D P hP x R b ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x (dgVerdierRightKanTarget A D P x b) =
        dgVerdierRightKanCofinalSliceProjection A D P hP x R b := by
  dsimp only [dgVerdierRightKanSliceRoofMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEndpointIso_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rightKanCofinalSliceRoofMap_projection]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
