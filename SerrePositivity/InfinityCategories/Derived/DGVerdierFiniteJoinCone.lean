module
public import SerrePositivity.InfinityCategories.Derived.TruncatedConeJoinMap
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTruncatedConeSuccessor
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-! # 実 Verdier 分母部分圏の有限図式の実 join 錐

概要：任意の有限単体集合から実分母部分圏への図式に、同じ部分圏内の実錐を供給する。
方針：有限性から非退化次元の上界を選び、切断錐の存在と実 join 構成を接続する。
規約：通常の圏の nerve だけに制限しない。使われ方：実分母添字の余 filtered 性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D] {P : Set D} {x : D}

/-- 任意の有限実分母図式は、同じ実分母部分圏内に実 join 錐を持つ。 -/
theorem dgVerdierFiniteJoinCone_nonempty {K : SSet.{max u v}} [K.Finite]
    (f : K ⟶ (dgVerdierOver A D P x : SSet)) : Nonempty (JoinCone f) := by
  obtain ⟨d, hd⟩ := K.hasDimensionLT_of_finite
  let := hd
  let : K.HasDimensionLE d := K.hasDimensionLT_of_le d (d + 1) (by omega)
  obtain ⟨C⟩ := dgVerdierTruncatedConeData_nonempty A D (f := f) (fun n => inferInstance) d
  exact ⟨C.joinCone⟩

end SerrePositivity.InfinityCategories
