module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberCofiberDecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeProjectionDifferential

/-! # 双対比較の原始元の第一成分の微分

概要：Q→fiber(f) の次数零成分 −T⋅snd(g) の微分と g による射影を求める。
方針：Leibniz 則と標準 cone の第二射影の微分を使う。
規約：g は fiber(f)→M、Q=cone(g)。使われ方：β3 の双対比較の合成の境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 双対比較の原始元の cone lift の第一成分。 -/
def dgModuleFiberCofiberHomotopyFirst (f : M ⟶ N) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) 0 :=
  -compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f)
    (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (zero_add 0)

/-- 第一成分の射影は第二 cone 射影の負。 -/
lemma dgModuleFiberCofiberHomotopyFirst_projection (f : M ⟶ N) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
      (dgModuleFiberCofiberHomotopyFirst A D f) (zero_add 0) =
      -moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) := by
  rw [dgModuleFiberCofiberHomotopyFirst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_right,
    compose_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT_projection, unit_compose]

/-- 第一成分の微分を二つの実行列項で表す。 -/
lemma dgModuleFiberCofiberHomotopyFirst_differential (f : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (moduleCone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)).d 0 1
      (dgModuleFiberCofiberHomotopyFirst A D f) =
      -compose A (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 1))
        (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (zero_add 1) +
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f)
        (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
          (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (add_zero 1))
        (add_zero 1) := by
  have ht : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f) =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberSectionFirst A D f)
        (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val (zero_add 1) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT_differential A D f
  have hs : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) =
      -compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
        (moduleConeFstElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (add_zero 1) := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSndElement_d A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection_cycle] at h
    exact h
  change _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleFiberCofiberHomotopyFirst A D f) = _
  have hn : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      (-compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f)
        (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (zero_add 0)) =
      -differential A (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberContractionT A D f)
        (moduleConeSndElement A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) (zero_add 0)) := map_neg _ _
  rw [dgModuleFiberCofiberHomotopyFirst, hn, _root_.SerrePositivity.DifferentialGraded.differential_compose, ht, hs,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompose_neg_right]
  simp only [Int.negOnePow_zero, one_smul]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
