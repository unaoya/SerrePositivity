module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeTargetHomExt

/-! # 双対比較の実合成と原始元の照合

概要：次数 −1 元の微分を降下比較の後の逆射と恒等の差と同定する。
方針：cone の二射影で比較し、fiber の分解恒等式を第一座標へ代入する。
規約：実閉加群射と全 Hom end の原始元。使われ方：β3 の双対比較辺の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 原始元の微分は降下の後の逆射と恒等の実閉零成分の差。 -/
lemma dgModuleFiberCofiberHomotopyElement_differential (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))).d (-1) 0
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyElement A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection A D f))).val -
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (𝟙 (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))))).val := by
  have hp : compose A (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection A D f))).val (zero_add 1) =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f))).val (zero_add 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection_cycle,
      compose_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection_fst]
  have hH := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
    (show 1 + (-1) = 0 by decide) (show (-1) + 1 = 0 by decide)
    (show 1 + (-1) + 1 = 1 by decide)
  have hF := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) (zero_add 0) (zero_add 1) (zero_add 1)
  have hT := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f)
    (add_zero 1) (zero_add 0) (add_zero 1)
  have hd : _root_.SerrePositivity.DifferentialGraded.compose A
      (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
        (show (-1) + 1 = 0 by decide))
      (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (add_zero 1) +
      _root_.SerrePositivity.DifferentialGraded.compose A
      (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
        (zero_add 0))
      (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (add_zero 1) =
      moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst_decomposition, unit_compose]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeTargetHom_ext A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) 0
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyElement_differential_coordinates,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, hp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_id, compose_unit,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyFirst_differential, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc_cycle,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeDescElement, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right, hH, hF, hT]
    have hs (a b c d : _root_.SerrePositivity.DifferentialGraded.GradedHom A
        (ForgetEnrichment.to (Complex A) (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) 1) (h : c + b = d) : -(-a + b) = c + a - d := by
      rw [← h]
      abel
    exact hs _ _ _ _ hd
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyElement_differential_coordinates,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection_cycle, compose_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection_snd,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_id, compose_unit, zero_sub]

/-- 実原始元を閉加群射のホモトピーとして保持する。 -/
def dgModuleFiberCofiberDescSectionHomotopy (f : M ⟶ N) :
    ModuleHomotopy A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberDesc A D f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSection A D f)
      (𝟙 _) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberHomotopyElement A D f,
    dgModuleFiberCofiberHomotopyElement_differential A D f⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
