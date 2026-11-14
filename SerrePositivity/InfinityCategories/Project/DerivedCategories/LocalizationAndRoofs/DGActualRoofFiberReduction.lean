module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofRelativeFiberReduction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteJoinCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGRoofFiberComparison

/-! # 実屋根比較の有限相対問題の共通 fiber 還元

概要：元屋根の境界と任意の商屋根図式を、同じ実分母頂点上の相対問題へ移す。
方針：商図式の射影に有限 join 錐を取り、二つの右ファイブレーションへ相対持ち上げする。
規約：境界・全体・比較は全時刻で厳密に整合する。使われ方：屋根比較の弱同値判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}

/-- 指定境界と商図式を共通の実分母 fiber へ移す還元データ。 -/
abbrev DGActualRoofFiberReduction (i : L ⟶ K)
    (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFiberReduction i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceProjection A D P x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y) a g

/-- 任意の有限商図式と指定元境界は、同じ実分母上へ全境界付きで輸送できる。 -/
theorem dgActualRoofFiberReduction_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [K.Finite]
    (i : L ⟶ K) [Mono i] (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y = i ≫ g) :
    Nonempty (DGActualRoofFiberReduction A D P x y i a g) := by
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierFiniteJoinCone_nonempty A D
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeFiberReduction_of_cone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_projection A D P x y) ha c

end SerrePositivity.InfinityCategories.Project.DerivedCategories
