module
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
概要：定値複体の通常閉単体は、同じ複体の頂点の恒等退化単体に厳密に一致する。
方針：零単体を対象で同定し、通常閉 nerve の全作用素への自然性を使う。
規約：全高次単体の等式。使われ方：二重 cone の恒等辺と恒等錐の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X : Complex A)

lemma complexConstantClosedNerveSimplex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin (n + 1))).obj X ⋙ complexToClosed A) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X).pullback (OrderHom.const _ (0 : Fin 1)) := by
  have h0 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin 1)).obj X ⋙ complexToClosed A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
    rfl
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex_pullback
    ((Functor.const (Fin 1)).obj X ⋙ complexToClosed A)
    (OrderHom.const (Fin (n + 1)) (0 : Fin 1))
  rw [h0] at h
  exact h

lemma complexConstantClosedNerveSimplex_yoneda (n : ℕ) :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin (n + 1))).obj X ⋙ complexToClosed A)) =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X) := by
  rw [complexConstantClosedNerveSimplex]
  change SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)).map
    (SimplexCategory.const _ _ 0).op ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X)) = _
  rw [← SSet.yonedaEquiv_symm_naturality_left, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

end SerrePositivity.EInfinity.ComplexLimits
