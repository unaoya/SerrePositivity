module
public import SerrePositivity.KST.SConstruction.DGModuleClosedChoices
public import SerrePositivity.KST.SConstruction.StableModels

/-! # 実操作に閉じた dg 加群部分圏の安定性
概要：実零加群・cone・fiber の閉性から全 dg 部分圏の nerve の安定性を得る。
方針：元の辺を保つ双カルテジアン四角形を選び、安定性の判定に渡す。
規約：H⁰ の三角性だけを安定性の代用にしない。使われ方：Perf の実 dg 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : _root_.SerrePositivity.DifferentialGraded.RightModule A D → Prop) (hP : DGModuleClosedOperations A D P)
include hP

/-- 実零加群を部分圏内に保持した零頂点の存在。 -/
lemma dgModuleClosedNerve_hasZeroVertex :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)) where
  exists_zero := by
    let Z : _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.RightModule A D) P := ⟨_root_.SerrePositivity.DifferentialGraded.zeroModule A D, hP.zero_mem⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Z, ?_, ?_⟩
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion A (RightModule A D) P
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).1
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion A (RightModule A D) P
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).2

/-- 実有限操作の閉性から得る全 dg 加群部分圏の安定性。 -/
lemma dgModuleClosedNerve_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)) := by
  let := dgModuleClosedNerve_hasZeroVertex A D P hP
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices
    (dgModuleClosed_bicartesian_fiber_exists A D P hP)
    (dgModuleClosed_bicartesian_cofiber_exists A D P hP)

/-- 全 dg 部分圏の native nerve を既存の S 構成の安定入力に束ねる。 -/
def dgModuleClosedStableModel : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGFullSubcategory (RightModule A D) P)
  quasicategory := inferInstance
  stable := dgModuleClosedNerve_isStable A D P hP

end SerrePositivity.KST.SConstruction
