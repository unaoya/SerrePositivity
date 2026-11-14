module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberHomProjections
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! # fiber の cofiber 比較の逆射の第一成分

概要：N から fiber(f) への閉次数1成分を作り、射影・零ホモトピーとの合成を求める。
方針：cone の右包含を shift の逆単位で戻して符号を反転する。
規約：第一成分の符号は負。使われ方：β3 の dual 比較の明示的逆射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- N→cone(f)[−1] の閉次数1成分。 -/
def dgModuleFiberCofiberSectionFirst (f : M ⟶ N) :
    GradedHom A (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) 1 :=
  -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0).symm (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)

/-- shift を外すと標準右包含の負になる。 -/
lemma dgModuleFiberCofiberSectionFirst_unshift (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0
      (dgModuleFiberCofiberSectionFirst A D f) = -moduleConeInrElement A D f := by
  rw [dgModuleFiberCofiberSectionFirst, map_neg, LinearEquiv.apply_symm_apply]

/-- 逆射の第一成分は閉じている。 -/
lemma dgModuleFiberCofiberSectionFirst_closed (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 1 2
      (dgModuleFiberCofiberSectionFirst A D f) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv_symm_differential A D
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0 (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
  have hi : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d 0 1
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) = 0 :=
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).property
  change (moduleHom A D (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 1 2
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0).symm
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)) =
    -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 1).symm
      ((_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d 0 1
          (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)) at h
  rw [hi, map_zero, neg_zero] at h
  change (moduleHom A D (ForgetEnrichment.to (Complex A) N) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 1 2
    (-(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0).symm
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)) = 0
  rw [map_neg, h, neg_zero]

/-- 標準射影との合成は零。 -/
lemma dgModuleFiberCofiberSectionFirst_projection (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
      (dgModuleFiberCofiberSectionFirst A D f) (add_zero 1) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_compose A D f 0, dgModuleFiberCofiberSectionFirst_unshift]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A) (moduleConeFstElement A D f)
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (zero_add 1)
  simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, moduleCone_inr_fst, neg_zero] using h

/-- 実零ホモトピーとの合成は N の dg 単位。 -/
lemma dgModuleFiberCofiberSectionFirst_nullHomotopy (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
      (dgModuleFiberCofiberSectionFirst A D f) (show 1 + (-1) = 0 by decide) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy_compose A D f 0, dgModuleFiberCofiberSectionFirst_unshift]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A) (moduleConeSndElement A D f)
    (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) 0)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (zero_add 0)
  simp only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] at h
  rw [h, _root_.SerrePositivity.DifferentialGraded.moduleCone_inr_snd, neg_neg]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
