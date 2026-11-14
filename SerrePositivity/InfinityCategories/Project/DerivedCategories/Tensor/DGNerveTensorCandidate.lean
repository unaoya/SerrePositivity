module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutTerm
/-!
概要：全切断点集合にわたる同じ符号付き有限和から、全次元の tensor 成分候補を構成する。
方針：同じ実 Hom と切断合成の次数を明示し、有限交差の点数で符号を定める。
規約：SimplexData の候補。HA 方程式と全面・退化への自然性は別途証明が必要。
使われ方：実 dg nerve の直積から tensor nerve への写像の全次元候補。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の二つの実 Hom 成分から、指定次数を持つ同じ tensor 成分候補を構成する。 -/
def dgNerveTensorHomCandidate {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) k :=
  ∑ S : (I.filter (fun j => a < j ∧ j < b)).powerset,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a b S.val k hk hI ha hb (by
      intro j hj
      have h := Finset.mem_powerset.mp S.property hj
      obtain ⟨hjI, haj, hjb⟩ := Finset.mem_filter.mp h
      exact ⟨hjI, haj, hjb⟩)
/-- 元の二つの実 Hom 成分から、指定次数を持つ同じ tensor 成分候補を構成する。 -/
def dgNerveTensorDataCandidate {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (DGTensorCategory R B C) n where
  obj i := (s.obj i, t.obj i)
  hom I a b k hI ha hb hk := dgNerveTensorHomCandidate R B C s t I a b k hk hI
    (by rw [ha]; exact Finset.isLeast_min' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (by rw [hb]; exact Finset.isGreatest_max' I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
