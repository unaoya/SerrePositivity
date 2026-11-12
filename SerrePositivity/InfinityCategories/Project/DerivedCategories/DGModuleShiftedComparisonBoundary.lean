module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepresentableDerivedPrimitives

/-! # シフト閉射の導来比較式から斉次差の実原始元へ

概要：ホモトピー射影的始域の二つのシフト閉射の導来等号を、元の斉次差の境界へ戻す。
方針：H⁰ の等号を実境界に戻し、右 shift の線形性と原始元の逆変換を使う。
規約：指定した二つの斉次元を保つ。使われ方：商の分数表示の具体的な比較境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 右 shift の斉次操作は差を保つ。 -/
lemma dgModuleHomRightShift_sub {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D} (n : ℤ)
    (f g : _root_.SerrePositivity.DifferentialGraded.GradedHom A M N n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n (f - g) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n f - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right _ _ _ _

/-- シフト閉射の比較式から、指定された元の斉次差の実原始元を回収する。 -/
lemma dgModuleShiftedComparison_exists_primitive {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
    (hM : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective A D M) (n k : ℤ) (hkn : k + 1 = n)
    (f g : M ⟶ N⟦n⟧)
    (p q : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) n)
    (hp : (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M (N⟦n⟧) f).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n p)
    (hq : (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M (N⟦n⟧) g).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n q)
    (he : (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map f = (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map g) :
    ∃ a : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).X k,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d k n a = p - q := by
  have hH : (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f = (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map g := by
    apply (_root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv A D hM _).injective
    rw [_root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv_map, _root_.SerrePositivity.DifferentialGraded.moduleProjectiveDerivedHomEquiv_map]
    exact he
  obtain ⟨h, hh⟩ := (_root_.SerrePositivity.DifferentialGraded.toHomotopy_map_eq_iff_boundary A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) f g).mp hH
  change (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
    (_root_.SerrePositivity.DifferentialGraded.shiftModule n (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N))).d (-1) 0 h =
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M (N⟦n⟧) f).val -
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M (N⟦n⟧) g).val at hh
  rw [hp, hq, ← dgModuleHomRightShift_sub] at hh
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_exists_primitive_iff A D n k hkn (p - q)).mp ⟨h, hh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
