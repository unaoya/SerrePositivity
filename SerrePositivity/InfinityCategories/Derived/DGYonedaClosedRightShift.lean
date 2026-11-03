module
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Derived.DGYonedaGradedPrimitives
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.InfinityCategories.DGNerve.FunctorMapping

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全次数 Yoneda は元の斉次閉元を閉元に送る。 -/
lemma dgYonedaGraded_closed {x y : D} (n : ℤ) (f : GradedHom A x y n)
    (hf : differential A f = 0) :
    differential A (D := RightModule A D) (x := representable A x) (y := representable A y)
      (n := n) ((yonedaHom A D x y).f n f) = 0 := by
  have h := ConcreteCategory.congr_hom ((yonedaHom A D x y).comm n (n + 1)) f
  change (moduleHom A D (representable A x) (representable A y)).d n (n + 1)
    ((yonedaHom A D x y).f n f) = (yonedaHom A D x y).f (n + 1) (differential A f) at h
  change (moduleHom A D (representable A x) (representable A y)).d n (n + 1)
    ((yonedaHom A D x y).f n f) = 0
  rw [h, hf, map_zero]

/-- 元の斉次閉元から作る代表加群のシフトへの実閉射。 -/
def dgYonedaClosedRightShift {x y : D} (n : ℤ) (f : GradedHom A x y n)
    (hf : differential A f = 0) :
    ForgetEnrichment.of (Complex A) (representable A x) ⟶
      (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D)⟦n⟧ :=
  dgModuleClosedRightShift A D n ((yonedaHom A D x y).f n f)
    (dgYonedaGraded_closed A D n f hf)

/-- 前合成後の閉射の cycle は、元の斉次前合成の Yoneda 右シフト。 -/
lemma dgYonedaClosedRightShift_precompose_cycle {q x y : D} (n : ℤ)
    (f : GradedHom A x y n) (hf : differential A f = 0)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (closedHomEquiv A (RightModule A D) _ _
      ((dgYoneda A D).onClosed.map s ≫ dgYonedaClosedRightShift A D n f hf)).val =
      dgModuleHomRightShift A D n ((yonedaHom A D q y).f n
        (compose A f (closedHomEquiv A D _ _ s).val (zero_add n))) := by
  rw [dgYonedaClosedRightShift, dgModuleClosedRightShift_precompose_cycle]
  congr 1
  have hs := congrArg Subtype.val ((dgYoneda A D).closedHomEquiv_map s)
  change (closedHomEquiv A (RightModule A D) _ _ ((dgYoneda A D).onClosed.map s)).val =
    (yonedaHom A D q x).f 0 (closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  exact (map_compose (dgYoneda A D) f (closedHomEquiv A D _ _ s).val (zero_add n)).symm

/-- シフト Hom end の原始元から、元の Hom の指定次数の原始元を回収する。 -/
lemma dgYonedaRightShift_exists_primitive {x y : D} (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A x y n)
    (h : (moduleHom A D (representable A x) (shiftModule n (representable A y))).X (-1))
    (hh : (moduleHom A D (representable A x) (shiftModule n (representable A y))).d (-1) 0 h =
      dgModuleHomRightShift A D n ((yonedaHom A D x y).f n f)) :
    ∃ a : GradedHom A x y k, (homObject A D x y).d k n a = f := by
  apply (dgYoneda_exists_gradedPrimitive_iff A D x y k n f).mp
  exact ⟨_, dgModuleHomRightShift_primitive A D n k hkn _ h hh⟩

end SerrePositivity.InfinityCategories
