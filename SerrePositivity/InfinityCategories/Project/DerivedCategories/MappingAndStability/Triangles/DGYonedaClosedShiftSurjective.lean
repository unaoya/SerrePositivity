module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomRightUnshift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGYonedaClosedRightShift

/-! # シフトへの閉代表加群射の元の斉次閉元による表示

概要：代表加群から代表加群の shift への任意の閉射を、元の dg Hom の斉次閉元から回収。
方針：射影で次数を戻して Yoneda 鎖同型を逆に使い、両逆関係で閉射自体の一致を得る。
規約：導来類だけでなく実際の閉射を回収。使われ方：全次数の商の分数表示の分子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表加群の shift への閉射は、元の斉次閉元から厳密に得られる。 -/
theorem dgYonedaClosedRightShift_surjective (x y : D) (n : ℤ)
    (g : ForgetEnrichment.of (Complex A) (representable A x) ⟶
      (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D)⟦n⟧) :
    ∃ a : GradedHom A x y n, ∃ ha : differential A a = 0,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n a ha = g := by
  let z := closedHomEquiv A (RightModule A D) _ _ g
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightUnshift A D n z.val
  have hb : (moduleHom A D (representable A x) (representable A y)).d n (n + 1) b = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightUnshift_closed A D n z.val z.property
  let e := (dgYonedaIso A x (representable A y)).symm
  let a : GradedHom A x y n := e.inv.f n b
  have ha : differential A a = 0 := by
    have h := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) b
    change differential A a = e.inv.f (n + 1)
      ((moduleHom A D (representable A x) (representable A y)).d n (n + 1) b) at h
    rw [hb, map_zero] at h
    exact h
  have he : (yonedaHom A D x y).f n a = b := by
    change e.hom.f n (e.inv.f n b) = b
    have h := congrArg (fun f => f.f n b) e.inv_hom_id
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ModuleCat.comp_apply, ModuleCat.id_apply] using h
  refine ⟨a, ha, ?_⟩
  apply (closedHomEquiv A (RightModule A D) _ _).injective
  apply Subtype.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_cycle, he]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_unshift A D n z.val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
