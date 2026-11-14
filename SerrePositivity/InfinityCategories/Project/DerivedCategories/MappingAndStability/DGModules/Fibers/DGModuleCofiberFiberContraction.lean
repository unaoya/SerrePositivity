module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleCofiberFiberRetraction

/-! # 標準 cofiber の fiber 比較の収縮の行列式

概要：第二 cone 射影と fiber の零ホモトピーの合成の微分と分解式を求める。
方針：Leibniz 則と全 Hom end の cone の行列恒等式を使う。
規約：実際の次数 −1 成分。使われ方：β3 の比較のもう一方の合成の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較の収縮に使う N への次数 −1 成分。 -/
def dgModuleCofiberFiberContractionN (f : M ⟶ N) :
    GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (-1) :=
  _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (add_zero (-1))

/-- 収縮の第一成分の微分は射影と元の射による差。 -/
lemma dgModuleCofiberFiberContractionN_differential (f : M ⟶ N) :
    (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d (-1) 0
        (dgModuleCofiberFiberContractionN A D f) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractElement A D f) (zero_add 0) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f) := by
  have hn : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (zero_add 0) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy_differential A D (moduleConeInr A D f)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle] at h
    exact h
  have hs : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
        (moduleConeFstElement A D f) (add_zero 1) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSndElement_d A D f
  have hfirst := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
    (show (-1) + 1 = 0 by decide) (add_zero 1) (show (-1) + 1 + 0 = 0 by decide)
  have hlast := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f)) (moduleConeInrElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f) (zero_add 0) (zero_add 0) (zero_add 0)
  rw [_root_.SerrePositivity.DifferentialGraded.moduleCone_inr_snd, _root_.SerrePositivity.DifferentialGraded.unit_compose] at hlast
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleCofiberFiberContractionN A D f) = _
  rw [dgModuleCofiberFiberContractionN, _root_.SerrePositivity.DifferentialGraded.differential_compose, hs, hn,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_left, ← hfirst, hlast]
  simp only [Int.negOnePow_zero, one_smul]
  rfl

/-- cone の二射影による分解を fiber の零ホモトピーへ適用した恒等式。 -/
lemma dgModuleCofiberFiberContractionN_decomposition (f : M ⟶ N) :
    compose A (moduleConeInlElement A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractElement A D f)
        (zero_add (-1)) +
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (dgModuleCofiberFiberContractionN A D f)
        (add_zero (-1)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f) := by
  have hfirst := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeFstElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) (show (-1) + 1 = 0 by decide) (add_neg_cancel 1)
    (show (-1) + 1 + (-1) = -1 by decide)
  have hlast := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (moduleConeSndElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f) (add_zero (-1)) (add_zero 0) (add_zero (-1))
  change _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)
      (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (by decide)) (zero_add (-1)) +
    _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
      (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D (moduleConeInr A D f)) (add_zero (-1)))
      (add_zero (-1)) = _
  rw [hfirst, hlast, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, moduleCone_decomposition, unit_compose]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
