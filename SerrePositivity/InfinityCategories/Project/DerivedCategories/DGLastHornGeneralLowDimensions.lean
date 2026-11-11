module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornCochains

/-! # 一般最後外ホーンの二未知データと既存三次・四次構成の一致

概要：一般残差 R と Q 挿入データは、三次・四次では検証済みの既存構成そのもの。
方針：欠面有限集合と次数を具体化し、三次では実 rhs の既存展開公式を使う。
規約：実データの厳密等式。使われ方：一般残差・符号計算と既存二未知方程式の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 次元三の一般欠面残差は、既存の同じ実三次ホーンの欠面残差。 -/
lemma dgGeneralLastHornMissingResidual_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingResidual σ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual
  have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_rhs_missing (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)

/-- 次元四の一般欠面残差も、既存の同じ実四次ホーンの残差。 -/
lemma dgGeneralLastHornMissingResidual_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual
  have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex 2 = {0, 1, 2, 3} := by decide
  simp only [hm]
  rfl

/-- 次元三の一般 Q 挿入は、既存の同じ実データの Q 挿入。 -/
lemma dgGeneralLastHornQData_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) (-1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornQData σ Q := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornQData _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedronWithQ
  have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm]
  rfl

/-- 次元四の一般 Q 挿入も、既存の同じ実データの Q 挿入。 -/
lemma dgGeneralLastHornQData_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornQData σ Q := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornQData
  have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex 2 = {0, 1, 2, 3} := by decide
  simp only [hm]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
