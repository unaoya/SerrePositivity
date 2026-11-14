module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierFiniteJoinCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiniteConeOpposite

/-! # 実 Verdier 分母添字の余 filtered 性

概要：実分母 over 圏を反転した ∞ 圏は、全有限図式に実余錐を持つ。
方針：有限 join 錐の存在を、反転による filtered 判定へ適用する。
規約：閉零圏の厳密な屋根添字へ置き換えない。使われ方：屋根比較の有限同時細分。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 実 Verdier 分母 over 圏の反転は filtered ∞ 圏。 -/
theorem dgVerdierOver_op_isFilteredInfinity (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_op_of_finiteCones _ (fun f => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierFiniteJoinCone_nonempty A D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
