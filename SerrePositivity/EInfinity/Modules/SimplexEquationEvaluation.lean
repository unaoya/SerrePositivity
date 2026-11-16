module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-!
概要：加群の dg 単体の全 HA 方程式を各対象での評価から回収する。
方針：元の Hom end の外延性と dg 関手の微分・合成・有限和の保存を使う。
規約：HA Construction 1.3.1.6、任意整数次数・全有限部分集合。
使われ方：M10 の同じ実三相データと全評価三角形の係数照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleSimplexData_equation_of_evaluation {n : ℕ}
    (s : SimplexData A (RightModule A D) n) (I : Finset (Fin (n + 1)))
    (h : ∀ x : D, (s.map (moduleEvaluationDG A D x)).Equation I) : s.Equation I := by
  intro a b k hI ha hb hk
  apply moduleHomElement_ext A D (M := s.obj a) (N := s.obj b)
  intro x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_differential
    (moduleEvaluationDG A D x) (s.hom I a b k hI ha hb hk)).trans
      ((h x a b k hI ha hb hk).trans
        (SimplexData.map_rhs s (moduleEvaluationDG A D x) I a b k hI ha hb hk).symm)

end SerrePositivity.EInfinity.Modules
