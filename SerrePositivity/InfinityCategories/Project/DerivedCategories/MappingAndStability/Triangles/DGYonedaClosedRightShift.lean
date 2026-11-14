module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGYonedaGradedPrimitives
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-! # 元の斉次 Hom の Yoneda shift と原始元の回収

概要：元の斉次閉元をシフトへの閉加群射へ写し、前合成と原始元を照合する。
方針：全次数 Yoneda の関手性、右シフトの微分式、Hom 鎖同型の反映を合成する。
規約：原始元は元の dg Hom に戻す。使われ方：β3 の有限個の高次障害の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 全次数 Yoneda は元の斉次閉元を閉元に送る。 -/
lemma dgYonedaGraded_closed {x y : D} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n)
    (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) (x := _root_.SerrePositivity.DifferentialGraded.representable A x) (y := _root_.SerrePositivity.DifferentialGraded.representable A y)
      (n := n) ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f n f) = 0 := by
  have h := ConcreteCategory.congr_hom ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).comm n (n + 1)) f
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A x) (_root_.SerrePositivity.DifferentialGraded.representable A y)).d n (n + 1)
    ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f n f) = (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f (n + 1) (_root_.SerrePositivity.DifferentialGraded.differential A f) at h
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A x) (_root_.SerrePositivity.DifferentialGraded.representable A y)).d n (n + 1)
    ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f n f) = 0
  rw [h, hf, map_zero]

/-- 元の斉次閉元から作る代表加群のシフトへの実閉射。 -/
def dgYonedaClosedRightShift {x y : D} (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n)
    (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x) ⟶
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A y) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)⟦n⟧ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift A D n ((yonedaHom A D x y).f n f)
    (dgYonedaGraded_closed A D n f hf)

/-- 前合成後の閉射の cycle は、元の斉次前合成の Yoneda 右シフト。 -/
lemma dgYonedaClosedRightShift_precompose_cycle {q x y : D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n) (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _
      ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s ≫ dgYonedaClosedRightShift A D n f hf)).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n ((yonedaHom A D q y).f n
        (_root_.SerrePositivity.DifferentialGraded.compose A f (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add n))) := by
  rw [dgYonedaClosedRightShift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_precompose_cycle]
  congr 1
  have hs := congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).closedHomEquiv_map s)
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _ ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)).val =
    (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose (dgYoneda A D) f (closedHomEquiv A D _ _ s).val (zero_add n)).symm

/-- シフト Hom end の原始元から、元の Hom の指定次数の原始元を回収する。 -/
lemma dgYonedaRightShift_exists_primitive {x y : D} (n k : ℤ) (hkn : k + 1 = n)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y n)
    (h : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A x) (_root_.SerrePositivity.DifferentialGraded.shiftModule n (_root_.SerrePositivity.DifferentialGraded.representable A y))).X (-1))
    (hh : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A x) (_root_.SerrePositivity.DifferentialGraded.shiftModule n (_root_.SerrePositivity.DifferentialGraded.representable A y))).d (-1) 0 h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n ((yonedaHom A D x y).f n f)) :
    ∃ a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k, (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d k n a = f := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYoneda_exists_gradedPrimitive_iff A D x y k n f).mp
  exact ⟨_, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_primitive A D n k hkn _ h hh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
