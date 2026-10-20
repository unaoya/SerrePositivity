module
public import SerrePositivity.InfinityCategories.Derived.RoofRelativeFiberReduction
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteJoinCone
public import SerrePositivity.InfinityCategories.Derived.DGRoofFiberComparison

/-! # 実屋根比較の有限相対問題の共通 fiber 還元

概要：元屋根の境界と任意の商屋根図式を、同じ実分母頂点上の相対問題へ移す。
方針：商図式の射影に有限 join 錐を取り、二つの右ファイブレーションへ相対持ち上げする。
規約：境界・全体・比較は全時刻で厳密に整合する。使われ方：屋根比較の弱同値判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {L K : SSet.{max u v}}

/-- 指定境界と商図式を共通の実分母 fiber へ移す還元データ。 -/
abbrev DGActualRoofFiberReduction (i : L ⟶ K)
    (a : L ⟶ dgRoofCorrespondence A D P x y)
    (g : K ⟶ dgQuotientRoofCorrespondence A D P x y) :=
  RoofRelativeFiberReduction i (dgRoofCorrespondenceProjection A D P x y)
    (dgQuotientRoofCorrespondenceProjection A D P x y) (dgRoofCorrespondenceMap A D P x y) a g

/-- 任意の有限商図式と指定元境界は、同じ実分母上へ全境界付きで輸送できる。 -/
theorem dgActualRoofFiberReduction_nonempty [IsDGPretriangulated A D] [K.Finite]
    (i : L ⟶ K) [Mono i] (a : L ⟶ dgRoofCorrespondence A D P x y)
    (g : K ⟶ dgQuotientRoofCorrespondence A D P x y)
    (ha : a ≫ dgRoofCorrespondenceMap A D P x y = i ≫ g) :
    Nonempty (DGActualRoofFiberReduction A D P x y i a g) := by
  obtain ⟨c⟩ := dgVerdierFiniteJoinCone_nonempty A D
    (g ≫ dgQuotientRoofCorrespondenceProjection A D P x y)
  exact roofRelativeFiberReduction_of_cone (dgRoofCorrespondenceMap_projection A D P x y) ha c

end SerrePositivity.InfinityCategories
