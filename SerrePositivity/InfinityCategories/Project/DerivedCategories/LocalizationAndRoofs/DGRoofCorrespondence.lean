module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierOver
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-! # 実 Verdier over 圏上の元の屋根と商側の屋根

概要：元の実分母 over ∞ 圏上に、同じ始域から y への実射の右ファイブレーションを作る。
方針：元の dg nerve と商の dg nerve の slice 射影を、実分母の始域写像で引き戻す。
規約：厳密 over nerve との同値や cofinality は仮定しない。使われ方：高次屋根の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の実分母と同じ始域から y への実射を持つ、実屋根の全空間。 -/
def dgRoofCorrespondence (P : Set D) (x y : D) : SSet.{max u v} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x)

/-- 元の実屋根から実分母 over 圏への射影。 -/
def dgRoofCorrespondenceProjection (P : Set D) (x y : D) :
    dgRoofCorrespondence A D P x y ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) :=
  pullback.snd _ _

/-- 元の実屋根の射影は右ファイブレーション。 -/
instance dgRoofCorrespondenceProjection_rightFibration (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (dgRoofCorrespondenceProjection A D P x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_pullback_snd _ _

/-- 元の実屋根の全空間は quasicategory。 -/
instance dgRoofCorrespondence_quasicategory (P : Set D) (x y : D) :
    Quasicategory (dgRoofCorrespondence A D P x y) :=
  quasicategory_of_innerFibration (dgRoofCorrespondenceProjection A D P x y)

/-- 同じ元の実分母上で、その始域の商像から y の商像への実射を持つ全空間。 -/
def dgQuotientRoofCorrespondence (P : Set D) (x y : D) : SSet.{max u v} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOverSource A D P x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P)

/-- 商側の実屋根から、同じ元の実分母 over 圏への射影。 -/
def dgQuotientRoofCorrespondenceProjection (P : Set D) (x y : D) :
    dgQuotientRoofCorrespondence A D P x y ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) :=
  pullback.snd _ _

/-- 商側の実屋根の射影も右ファイブレーション。 -/
instance dgQuotientRoofCorrespondenceProjection_rightFibration (P : Set D) (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (dgQuotientRoofCorrespondenceProjection A D P x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_pullback_snd _ _

/-- 商側の実屋根の全空間も quasicategory。 -/
instance dgQuotientRoofCorrespondence_quasicategory (P : Set D) (x y : D) :
    Quasicategory (dgQuotientRoofCorrespondence A D P x y) :=
  quasicategory_of_innerFibration (dgQuotientRoofCorrespondenceProjection A D P x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
