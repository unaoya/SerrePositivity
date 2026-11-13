module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberContraction

/-! # fiber の cofiber 比較の二成分の分解恒等式

概要：逆射の第一成分と零ホモトピー、T と射影の合成の和は fiber の単位。
方針：shift を外し cone の二射影の分解恒等式へ戻す。
規約：全 Hom end の実単位を使う。使われ方：β3 の双対比較の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 逆射の第一成分と収縮成分は fiber の実単位を分解する。 -/
lemma dgModuleFiberCofiberSectionFirst_decomposition (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
        (show (-1) + 1 = 0 by decide) +
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
        (zero_add 0) = (unitElement A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).val := by
  let out : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1) := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
  have ha : compose A out (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
      (show 1 + (-1) = 0 by decide) = -moduleConeInrElement A D f :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst_unshift A D f
  have ht : compose A out (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f) (zero_add (-1)) =
      moduleConeInlElement A D f :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1)).apply_symm_apply _
  have h1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f) out (show (-1) + 1 = 0 by decide)
    (show 1 + (-1) = 0 by decide) (show (-1) + 1 + (-1) = -1 by decide)
  have h2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f) out (zero_add 0) (zero_add (-1)) (zero_add (-1))
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1)).injective
  rw [map_add]
  change _root_.SerrePositivity.DifferentialGraded.compose A out _ (zero_add (-1)) + _root_.SerrePositivity.DifferentialGraded.compose A out _ (zero_add (-1)) =
    compose A out (unitElement A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).val (zero_add (-1))
  rw [h1, h2, ha, ht, compose_unit, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_left,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_right, neg_neg]
  have hc1 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) out (moduleConeSndElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (add_zero (-1)) (add_zero 0) (add_zero (-1))
  have hc2 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) out (moduleConeFstElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) (show (-1) + 1 = 0 by decide) (add_neg_cancel 1)
    (show (-1) + 1 + (-1) = -1 by decide)
  have hc : _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f) (add_zero 0) +
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f) (add_neg_cancel 1) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).val :=
    (add_comm _ _).trans (_root_.SerrePositivity.DifferentialGraded.moduleCone_decomposition A D f)
  rw [hc1, hc2, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, hc, unit_compose]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
