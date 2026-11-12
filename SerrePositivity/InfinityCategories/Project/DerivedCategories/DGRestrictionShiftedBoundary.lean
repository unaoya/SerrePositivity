module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleRightShiftPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionGradedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaClosedRightShift

/-! # 像の斉次境界性からシフト比較後の導来零性へ

概要：dg 関手の像で境界となる斉次閉元は、シフトされた制限代表比較の後で導来零。
方針：全次数 Yoneda 評価で原始元を戻し、右 shift の後合成の自然性で閉射へ移す。
規約：前三角性・平坦性・モデル圏仮定は不要。使われ方：商で境界となる有限族の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 像で境界となる斉次閉元は、シフトされた制限代表比較後に主導来零となる。 -/
lemma dgRestrictionShiftedComparison_zero_of_boundary {x y : D} (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A x y n) (hf : differential A f = 0)
    (hb : ∃ b : GradedHom A (F.obj x) (F.obj y) k,
      (homObject A E (F.obj x) (F.obj y)).d k n b = (F.map x y).f n f) :
    (moduleToDerived A D).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n f hf ≫
        (representableRestrictionMap A D E F y)⟦n⟧') = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_postcompose_zero_of_primitive A D
    (representable_homotopicallyProjective A D x) n k hkn
    ((yonedaHom A D x y).f n f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaGraded_closed A D n f hf)
    (representableRestrictionMap A D E F y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedComparison_exists_primitive A D E F k n f hb)

/-- シフト比較後の導来零性は、元の dg 関手の像の斉次境界性と同値。 -/
lemma dgRestrictionShiftedComparison_zero_iff_boundary {x y : D} (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A x y n) (hf : differential A f = 0) :
    (moduleToDerived A D).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n f hf ≫
        (representableRestrictionMap A D E F y)⟦n⟧') = 0 ↔
      ∃ b : GradedHom A (F.obj x) (F.obj y) k,
        (homObject A E (F.obj x) (F.obj y)).d k n b = (F.map x y).f n f := by
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveDerived_zero_iff_primitive A D
      (representable_homotopicallyProjective A D x) _).mp hz
    have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_postcompose_cycle A D n
      ((yonedaHom A D x y).f n f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaGraded_closed A D n f hf)
      (representableRestrictionMap A D E F y)
    let u := (eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
      (representableRestrictionMap A D E F y)).f n ((yonedaHom A D x y).f n f)
    have hp := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_exists_primitive_iff A D n k hkn u).mp
      ⟨h, hh.trans hc⟩
    have hb := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexIso_exists_primitive_iff A
      (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom k n u).mpr hp
    have he := congrArg (fun a => a.f n f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedComparison_evaluation A D E F x y)
    change (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom.f n u =
      (F.map x y).f n f at he
    rw [he] at hb
    exact hb
  · exact dgRestrictionShiftedComparison_zero_of_boundary A D E F n k hkn f hf

end SerrePositivity.InfinityCategories.Project.DerivedCategories
