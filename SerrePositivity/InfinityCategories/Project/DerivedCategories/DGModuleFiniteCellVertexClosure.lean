module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleVertexShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleH0Property
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomotopyFiniteCellGeneration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoGeneration

/-! # 有限 cell の K(D) 内の像と実安定閉包の一致

概要：指定代表加群で生成した実安定閉包は、retract を加えない有限 cell の K(D) 内の像と一致。
方針：実 cofiber と標準 cone の両方向の対象条件比較を、双方の最小生成性へ適用する。
規約：全 dg 加群の native nerve での主張。使われ方：有限 cell roof の実分母条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 指定 dg 対象の代表加群の実頂点の集合。 -/
def dgModuleGeneratorVertices (S : Set D) : Set ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌) :=
  (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable A x)) '' S

/-- 指定代表加群の実安定閉包と有限 cell の K(D) 内の本質像への所属は同値。 -/
theorem dgModule_stableVertexClosure_iff_finiteCell (S : Set D) (M : _root_.SerrePositivity.DifferentialGraded.RightModule A D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (dgModuleGeneratorVertices A D S) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) ↔
      _root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D S
        ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) M)) := by
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)
  let R := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (dgModuleGeneratorVertices A D S)
  constructor
  · intro hM
    have hle : R ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D (homotopyFiniteCellOver A D S) := by
      refine (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
        (dgModuleGeneratorVertices A D S)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHoProperty A D (homotopyFiniteCellOver A D S))).mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver A D S).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D)
        (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver_representable A D x hx)
    exact hle (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) hM
  · intro hM
    have hle : homotopyFiniteCellOver A D S ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleH0Property A D R := by
      refine (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyFiniteCellOver_le_iff_generators A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleH0Property A D R) S).mpr ?_
      intro x hx
      change R (E.inverse.obj (E.functor.obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (representable A x)))))
      exact R.prop_of_iso (E.unitIso.app _)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem ⟨x, hx, rfl⟩)
    exact R.prop_of_iso (E.unitIso.app (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M))).symm
      (hle _ hM)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
