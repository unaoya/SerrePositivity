module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGRoofFiberComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOverRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofLocallyConstantPullback

/-! # 商側の実屋根の左右ファイブレーション性

概要：平坦商での実屋根の射影は、右だけでなく左ファイブレーションでもある。
方針：実分母の全細分の始域写像が商で可逆になるので、core 上の全ホーン充填へ戻す。
規約：元の厳密添字の filteredness は使わない。使われ方：固定商 Hom と実屋根の比較。
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

/-- 商側の実屋根の射影は、実分母 over ∞ 圏上の左ファイブレーションでもある。 -/
lemma dgQuotientRoofCorrespondenceProjection_leftFibration (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRightFibration_pullback_leftFibration_of_inverts
  intro σ
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource_quotient_inverts A D P x hP (Set.mem_univ σ)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex σ).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P).app (Opposite.op ⦋1⦌) σ)).edge from rfl)).mp h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
