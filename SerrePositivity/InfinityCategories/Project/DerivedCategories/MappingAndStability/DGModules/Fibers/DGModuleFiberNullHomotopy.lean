module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberObject

/-! # shifted cone の射影の合成を零にする全 Hom end のホモトピー

概要：標準 nullhomotopy の微分が射影と元の加群射の合成に等しい。
方針：第二射影の微分と shift 単位の閉性に通常順の Leibniz 則を使う。
規約：符号を含む実際の次数 −1 成分で主張する。使われ方：β3 の fiber 四角形の二単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 標準 nullhomotopy の微分は fiber 射影と元の閉加群射の合成の成分。 -/
lemma dgModuleFiberNullHomotopy_differential (f : M ⟶ N) :
    (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (ForgetEnrichment.to (Complex A) N)).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f ≫ f))).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp A D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle]
  change differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy, show differential (D := RightModule A D) A
      (-_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
        (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
        (by decide)) =
      -_root_.SerrePositivity.DifferentialGraded.differential A (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
        (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
        (by decide)) from map_neg _ _, _root_.SerrePositivity.DifferentialGraded.differential_compose]
  have hsnd : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
        (moduleConeFstElement A D f) (add_zero 1) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSndElement_d A D f
  have hout : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))) = 0 :=
    _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement_d A D (-1) _
  rw [hsnd, hout, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  have hneg := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left (A := A)
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) 1)
    (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
      (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f) (add_zero 1))
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (show (-1) + 1 = 0 by decide)
  simp only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose] at hneg
  rw [hneg, neg_neg]
  exact (_root_.SerrePositivity.DifferentialGraded.compose_assoc A
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
      (show (-1) + 1 + 0 = 0 by decide)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
