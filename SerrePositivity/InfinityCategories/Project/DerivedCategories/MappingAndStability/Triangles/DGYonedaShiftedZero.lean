module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGYonedaClosedRightShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepresentableDerivedPrimitives

/-! # 斉次 cycle の境界性と shift 閉射の導来零性

概要：元の斉次閉元の境界性を、代表加群のシフトへの実閉射の導来零性と同定する。
方針：射影性、右シフトの境界の保存・反映、全 Hom Yoneda 同型をつなぐ。
規約：前三角性・平坦性は不要。使われ方：商の斉次境界を導来比較へ戻す入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- シフト閉射の主導来零性は、元の斉次 Hom の具体的な境界性と同値。 -/
lemma dgYonedaClosedRightShift_zero_iff_primitive {x y : D} (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A x y n) (hf : differential A f = 0) :
    (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n f hf) = 0 ↔
      ∃ a : GradedHom A x y k, (homObject A D x y).d k n a = f := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveDerived_zero_iff_primitive A D
    (representable_homotopicallyProjective A D x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedRightShift A D n f hf)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_cycle A D n ((yonedaHom A D x y).f n f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaGraded_closed A D n f hf)
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := he.mp hz
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaRightShift_exists_primitive A D n k hkn f h (hh.trans hc)
  · intro hp
    obtain ⟨a, ha⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYoneda_exists_gradedPrimitive_iff A D x y k n f).mpr hp
    obtain ⟨h, hh⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_exists_primitive_iff A D n k hkn
      ((yonedaHom A D x y).f n f)).mpr ⟨a, ha⟩
    exact he.mpr ⟨h, hh.trans hc.symm⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
