module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierFiniteJoinCone
public import SerrePositivity.InfinityCategories.Derived.FiniteConeOpposite

/-! # 実 Verdier 分母添字の余 filtered 性

概要：実分母 over 圏を反転した ∞ 圏は、全有限図式に実余錐を持つ。
方針：有限 join 錐の存在を、反転による filtered 判定へ適用する。
規約：閉零圏の厳密な屋根添字へ置き換えない。使われ方：屋根比較の有限同時細分。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 実 Verdier 分母 over 圏の反転は filtered ∞ 圏。 -/
theorem dgVerdierOver_op_isFilteredInfinity (P : Set D) (x : D) :
    F2.IsFilteredInfinity (dgVerdierOver A D P x : SSet.{max u v}).op :=
  isFilteredInfinity_op_of_finiteCones _ (fun f => dgVerdierFiniteJoinCone_nonempty A D f)

end SerrePositivity.InfinityCategories
