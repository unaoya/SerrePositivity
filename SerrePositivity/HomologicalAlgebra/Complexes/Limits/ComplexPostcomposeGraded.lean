module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ComplexPinchedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionComponents

/-!
概要：元の複体射の閉 cochain との dg 合成を、同じ Hom 後合成へ回収する。
方針：同じ豊穣後合成の次数成分式と元の複体後合成との一致を使う。
規約：任意の整数次数と同じ実射を保持する。
使われ方：cone の最後の切断合成を元の普遍 cochain の像へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexPostcompose_graded (X : Complex A) {P Q : Complex A} (f : P ⟶ Q)
    (k : ℤ) (v : GradedHom A X P k) :
    compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f)).val v
      (add_zero k) = (homPostcompose X f).f k v := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_f A (Complex A) (x := X) ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f) k v
  rw [_root_.SerrePositivity.ComplexLimits.complexToClosed_postcomposition] at h
  exact h.symm

end SerrePositivity.ComplexLimits
