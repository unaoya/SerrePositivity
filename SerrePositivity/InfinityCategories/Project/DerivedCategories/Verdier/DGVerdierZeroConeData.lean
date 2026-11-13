module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TruncatedJoinConeData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierDiagramVertexCone

/-! # 実分母図式の有限次数錐の零次初期段階

概要：既存の共通実頂点錐を、全頂点上の零次錐データへ移す。
方針：実脚の source・target を共通 apex と零面に読み、残る高次条件は空とする。
規約：高次錐の存在はここでは主張しない。使われ方：有限次数帰納の初期値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}

/-- 指定実頂点錐から得る、全図式頂点上の零次錐データ。 -/
def dgVerdierZeroConeData (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f 0 where
  apex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x C.denominator
  simplex n hn σ := by
    have he : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    exact (C.leg σ).edge
  face_zero n hn σ := by
    have he : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    exact (C.leg σ).tgt_eq
  first_vertex n hn σ := by
    have he : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).map
      (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op (C.leg σ).edge = _
    rw [show SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ (1 : Fin 2) from by decide]
    exact (C.leg σ).src_eq
  face_positive n hn := by omega
  degeneracy_positive n hn := by omega

/-- 図式頂点が有限なら、実分母部分圏内の零次錐データは存在する。 -/
theorem dgVerdierZeroConeData_nonempty [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] [Finite (K _⦋0⦌)] :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f 0) := by
  obtain ⟨C⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramVertexCone_nonempty A D P x f
  exact ⟨dgVerdierZeroConeData A D C⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
