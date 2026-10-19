module
public import SerrePositivity.InfinityCategories.Derived.DGRoofFiberComparison
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOverRefinement
public import SerrePositivity.InfinityCategories.Derived.RoofLocallyConstantPullback

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商側の実屋根の射影は、実分母 over ∞ 圏上の左ファイブレーションでもある。 -/
lemma dgQuotientRoofCorrespondenceProjection_leftFibration (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D) :
    LeftFibration (dgQuotientRoofCorrespondenceProjection A D P x y) := by
  apply roofRightFibration_pullback_leftFibration_of_inverts
  intro σ
  have h := dgVerdierOverSource_quotient_inverts A D P x hP (Set.mem_univ σ)
  exact (isInvertibleEdge_congr (show
    ((edgeOfSimplex σ).map ((truncation 2).map
      (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P))).edge =
    (edgeOfSimplex ((dgVerdierOverSource A D P x ≫
      dgQuotientNerveProjection A D P).app (Opposite.op ⦋1⦌) σ)).edge from rfl)).mp h

end SerrePositivity.InfinityCategories
