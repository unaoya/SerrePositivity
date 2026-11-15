module
public import SerrePositivity.EInfinity.Modules.SimplexAugmentation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion

/-!
概要：定値加群の通常閉単体は同じ頂点の恒等退化単体に一致する。
方針：零単体を対象で同定し、元の閉 nerve の全作用素の自然性を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、元の全単体。
使われ方：同じ二重 cone の恒等辺と恒等錐の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (M : ModuleCategory A D)

lemma moduleConstantClosedNerveSimplex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      ((Functor.const (Fin (n + 1))).obj M) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
      (ForgetEnrichment.to (Complex A) M)).pullback (OrderHom.const _ (0 : Fin 1)) := by
  have h0 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      ((Functor.const (Fin 1)).obj M) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
        (ForgetEnrichment.to (Complex A) M) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A D)).injective
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback
    ((Functor.const (Fin 1)).obj M) (OrderHom.const (Fin (n + 1)) (0 : Fin 1))
  rw [h0] at h
  exact h

lemma moduleConstantClosedNerveSimplex_yoneda (n : ℕ) :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A D))).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
        ((Functor.const (Fin (n + 1))).obj M)) =
    SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A D)).symm
      (ForgetEnrichment.to (Complex A) M)) := by
  rw [moduleConstantClosedNerveSimplex]
  change SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A D)).map
      (SimplexCategory.const _ _ 0).op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A D)).symm
        (ForgetEnrichment.to (Complex A) M))) = _
  rw [← SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

end SerrePositivity.EInfinity.Modules
