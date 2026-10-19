module
public import SerrePositivity.InfinityCategories.Derived.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableDerivedPrimitives

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 右 shift の斉次操作は差を保つ。 -/
lemma dgModuleHomRightShift_sub {M N : RightModule A D} (n : ℤ)
    (f g : GradedHom A M N n) :
    dgModuleHomRightShift A D n (f - g) =
      dgModuleHomRightShift A D n f - dgModuleHomRightShift A D n g :=
  compose_sub_right _ _ _ _

/-- シフト閉射の比較式から、指定された元の斉次差の実原始元を回収する。 -/
lemma dgModuleShiftedComparison_exists_primitive {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (n k : ℤ) (hkn : k + 1 = n)
    (f g : M ⟶ N⟦n⟧)
    (p q : GradedHom A (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) n)
    (hp : (closedHomEquiv A (RightModule A D) M (N⟦n⟧) f).val =
      dgModuleHomRightShift A D n p)
    (hq : (closedHomEquiv A (RightModule A D) M (N⟦n⟧) g).val =
      dgModuleHomRightShift A D n q)
    (he : (moduleToDerived A D).map f = (moduleToDerived A D).map g) :
    ∃ a : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X k,
      (moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N)).d k n a = p - q := by
  have hH : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g := by
    apply (moduleProjectiveDerivedHomEquiv A D hM _).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map]
    exact he
  obtain ⟨h, hh⟩ := (toHomotopy_map_eq_iff_boundary A (RightModule A D) f g).mp hH
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (shiftModule n (ForgetEnrichment.to (Complex A) N))).d (-1) 0 h =
      (closedHomEquiv A (RightModule A D) M (N⟦n⟧) f).val -
        (closedHomEquiv A (RightModule A D) M (N⟦n⟧) g).val at hh
  rw [hp, hq, ← dgModuleHomRightShift_sub] at hh
  exact (dgModuleHomRightShift_exists_primitive_iff A D n k hkn (p - q)).mp ⟨h, hh⟩

end SerrePositivity.InfinityCategories
