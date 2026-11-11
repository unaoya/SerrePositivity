module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornExpandedSolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornRefinedResiduals

/-! # 一般最上位残差 K と後合成の既存三次・四次との照合

概要：一般の既知 K と最後辺による Q 項は、三次・四次の既存二未知微分式の同じ成分。
方針：三次では元の rhs 展開と未知欠面の零、四次では既存の最上位 rhs 公式を使う。
規約：符号と元の射を厳密に保持。使われ方：一般残差 cone の低次検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 三次の一般 K は、既存の実三次ホーンの同じ既知残差。 -/
lemma dgGeneralLastHornTopResidual_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTopResidual σ := by
  have hQ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingHom_zero σ
  have hm : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornMissingIndex 1 = {0, 1, 2} := by decide
  simp only [hm] at hQ
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).tripleHom 0 1 2 (by decide) (by decide) = 0 := hQ
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTetrahedron_rhs_top (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ)
  rw [ht, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero] at hr
  exact hr

/-- 四次の一般 K も、既存の実四次ホーンの同じ既知残差。 -/
lemma dgGeneralLastHornTopResidual_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHorn_rhs_top σ

/-- 三次の一般 Q 後合成は、既存二未知微分式の同じ最後辺との合成。 -/
lemma dgGeneralLastHornPostcomposeQ_three
    (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) (-1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ Q =
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide)) Q (by decide) := rfl

/-- 四次の一般 Q 後合成も、既存二未知微分式の同じ最後辺との合成。 -/
lemma dgGeneralLastHornPostcomposeQ_four
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ Q =
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide)) Q (by decide) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
