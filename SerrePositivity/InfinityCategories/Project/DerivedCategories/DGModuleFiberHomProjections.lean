module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberHomInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeLiftProjections

/-! # fiber Hom 座標と実射影の一致

概要：二成分の逆座標を射影・零ホモトピーで回収する。
方針：shift の閉斉次単位の逆法則と cone lift の射影を使う。
規約：第二成分の次数は一段低い。使われ方：β3 の実 slice の二脚と三角形の方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {T M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 全 Hom end の合成は左因子の符号を保つ。 -/
lemma dgModuleCompose_neg_left {X Y Z : _root_.SerrePositivity.DifferentialGraded.RightModule A D} {p q r : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom A Y Z q) (z : _root_.SerrePositivity.DifferentialGraded.GradedHom A X Y p) (h : p + q = r) :
    _root_.SerrePositivity.DifferentialGraded.compose A (-g) z h = -compose A g z h := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left (A := A) (0 : GradedHom A Y Z q) g z h
  simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose] using he

/-- fiber 射影との合成は shift を外した第一 cone 射影。 -/
lemma dgModuleFiberProjection_compose (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1)) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) z (add_zero (n + 1)) =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) n z) rfl :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) z
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (_root_.SerrePositivity.DifferentialGraded.moduleConeFstElement A D f) (show n + 1 + (-1) = n by omega)
    (show (-1) + 1 = 0 by decide) rfl).symm

/-- fiber の零ホモトピーとの合成は shift を外した第二 cone 射影の負。 -/
lemma dgModuleFiberNullHomotopy_compose (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1)) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) z (by omega) =
      -_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNegativeShiftTargetHomEquiv A D (ForgetEnrichment.to (Complex A) T)
          (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) n z) (add_zero n) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy, dgModuleCompose_neg_left]
  exact congrArg Neg.neg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := A) z
    (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement A D (-1) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))
    (_root_.SerrePositivity.DifferentialGraded.moduleConeSndElement A D f) (show n + 1 + (-1) = n by omega)
    (show (-1) + 0 = -1 by decide) (add_zero n)).symm

/-- fiber への逆座標の射影成分は指定した第一成分。 -/
lemma dgModuleFiberHomCoordinates_symm_projection (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n).symm (a, b)) (add_zero (n + 1)) = a := by
  rw [dgModuleFiberProjection_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm,
    LinearEquiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_fst A D f n a (-b)

/-- fiber への逆座標の零ホモトピー成分は指定した第二成分。 -/
lemma dgModuleFiberHomCoordinates_symm_nullHomotopy (f : M ⟶ N) (n : ℤ) (a) (b) :
    compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n).symm (a, b)) (by omega) = b := by
  rw [dgModuleFiberNullHomotopy_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm,
    LinearEquiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeLiftElement_snd, neg_neg]

/-- fiber Hom の第一座標は実際の射影との合成。 -/
lemma dgModuleFiberHomCoordinates_fst (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).1 =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f) z (add_zero (n + 1)) := by
  have h := dgModuleFiberHomCoordinates_symm_projection A D f n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).2
  simpa only [Prod.mk.eta, LinearEquiv.symm_apply_apply] using h.symm

/-- fiber Hom の第二座標は実際の零ホモトピーとの合成。 -/
lemma dgModuleFiberHomCoordinates_snd (f : M ⟶ N) (n : ℤ)
    (z : GradedHom A (ForgetEnrichment.to (Complex A) T) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).2 =
      compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) z (by omega) := by
  have h := dgModuleFiberHomCoordinates_symm_nullHomotopy A D f n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D T f n z).2
  simpa only [Prod.mk.eta, LinearEquiv.symm_apply_apply] using h.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
