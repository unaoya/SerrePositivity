module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource

/-!
概要：実複体の dg 単体の全斉次成分に厳密に両立する、指定終端への augmentation を束ねる。
方針：対象ごとの元の chain map と、全有限集合での同じ合成式を記録する。
規約：終端を加えた単体の存在は仮定しない。使われ方：実右 cone の HA 方程式の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

structure ComplexSimplexAugmentation {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) (X : Complex A) where
  app : ∀ i, s.obj i ⟶ X
  hom_naturality : ∀ (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
      (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
      (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)),
      compose A (closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (app b))).val
        (s.hom I a b k hI ha hb hk) (add_zero k) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (app a)) k

def _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation.cycle {n : ℕ} {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation A s X) (i : Fin (n + 1)) :
    zeroCycles (homObject A (Complex A) (s.obj i) X) :=
  closedHomEquiv A (Complex A) _ _ ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (η.app i))

lemma _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation.cycle_closed {n : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n} {X : Complex A}
    (η : _root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation A s X) (i : Fin (n + 1)) :
    differential A (_root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation.cycle A η i).val = 0 :=
  (_root_.SerrePositivity.ComplexLimits.ComplexSimplexAugmentation.cycle A η i).property

end SerrePositivity.ComplexLimits
