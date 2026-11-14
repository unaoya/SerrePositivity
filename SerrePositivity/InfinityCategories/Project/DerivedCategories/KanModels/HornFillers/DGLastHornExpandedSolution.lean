module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornTopRhsDifference

/-! # 一般最後外ホーンの K と Q に分解した二未知解

概要：Q の微分式と、A の微分が K＋最後辺∘Q である式から、同じ一般実充填を得る。
方針：最上位 rhs の一般分解を既存の型付き解のフィールドへ接続する。
規約：二微分式を明示入力にする。使われ方：残差 cone の二座標から実ホーン充填へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}

/-- K と最後辺による後合成へ分解した二微分式から、同じ一般二未知解を構成する。 -/
def dgGeneralLastHornSolutionOfCochains
    (Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ)))
    (dQ : differential A Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ)
    (a : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1))
    (da : differential A a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ where
  Q := Q
  differential_Q := dQ
  a := a
  differential_a := da.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_rhs_top σ Q).symm

/-- 任意の一般解の A 微分も、同じ既知 K と最後辺による Q の後合成に分解される。 -/
lemma DGGeneralLastHornSolution.differential_a_expanded (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ) :
    differential A S.a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornTopResidual σ + _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornPostcomposeQ σ S.Q :=
  S.differential_a.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_rhs_top σ S.Q)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
