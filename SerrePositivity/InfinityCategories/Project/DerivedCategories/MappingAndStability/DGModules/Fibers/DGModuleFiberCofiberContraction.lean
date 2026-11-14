module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberCofiberSectionFirst
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberNullHomotopy

/-! # 双対比較の収縮の次数零成分

概要：M→fiber(f) の次数零成分 T と、その微分・射影成分を計算する。
方針：shift の閉斉次単位を cone の左包含へ合成する。
規約：dT は逆射の第一成分と f の合成。使われ方：β3 の双対比較の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 全 Hom end の合成は右因子の負号を保つ。 -/
lemma dgModuleCompose_neg_right {X Y Z : _root_.SerrePositivity.DifferentialGraded.RightModule A D} {p q r : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A Y Z q) (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A X Y p) (h : p + q = r) :
    _root_.SerrePositivity.DifferentialGraded.compose A g (-z) h = -compose A g z h := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A) g (0 : GradedHom A X Y p) z h
  simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] using he

/-- 収縮の M→fiber(f) の次数零成分。 -/
def dgModuleFiberCofiberContractionT (f : M ⟶ N) :
    GradedHom A (ForgetEnrichment.to (Complex A) M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1)).symm
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)

/-- T の標準射影は M の単位。 -/
lemma dgModuleFiberCofiberContractionT_projection (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
      (dgModuleFiberCofiberContractionT A D f) (zero_add 0) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_compose A D f (-1), dgModuleFiberCofiberContractionT,
    LinearEquiv.apply_symm_apply, _root_.SerrePositivity.DifferentialGraded.moduleCone_inl_fst]

/-- T の零ホモトピー成分は零。 -/
lemma dgModuleFiberCofiberContractionT_nullHomotopy (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
      (dgModuleFiberCofiberContractionT A D f) (zero_add (-1)) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy_compose A D f (-1), dgModuleFiberCofiberContractionT,
    LinearEquiv.apply_symm_apply, _root_.SerrePositivity.DifferentialGraded.moduleCone_inl_snd, neg_zero]

/-- T の微分は逆射の第一成分と元の射の合成。 -/
lemma dgModuleFiberCofiberContractionT_differential (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 0 1
      (dgModuleFiberCofiberContractionT A D f) =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 1) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv_symm_differential A D
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) (-1) (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)
  have hi : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f) =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (f ≫ _root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val :=
    _root_.SerrePositivity.DifferentialGraded.moduleConeInlElement_d A D f
  rw [hi, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedCycle_comp] at hd
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 0 1
    (dgModuleFiberCofiberContractionT A D f) =
    -_root_.SerrePositivity.DifferentialGraded.compose A
      (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
      (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 0))
      (zero_add 1) at hd
  rw [hd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_left]
  exact congrArg Neg.neg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A)
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftInElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (zero_add 0) (zero_add 1) (zero_add 1))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
