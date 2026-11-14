module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornCochains

/-! # 実三次最後外ホーンの最後の閉辺

概要：二未知式の後合成に現れる最後の辺を、実ホーンから回収した閉零射として構成する。
方針：二点集合の既知方程式を取り、内部点が無いことから閉性を得る。
規約：分母性は別に照合する。使われ方：閉辺の cone 内の残差と原始元の計算。
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
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実ホーンの既知データの最後の次数零辺は閉じている。 -/
lemma dgLastHornFinalEdge_closed :
    differential A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide)) = 0 := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ {2, 3} 2 3 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine hd.trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj : j.val = (2 : Fin 4) ∨ j.val = 3 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using j.property
  rcases hj with h | h
  · simp [h]
  · simp [h]

/-- 最後の辺を、二未知式で使う元の Hom 複体の閉零 cycle として読む。 -/
def dgLastHornFinalCycle : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 2 3 (by decide), dgLastHornFinalEdge_closed σ⟩

/-- 最後の辺を、元の閉零 dg 圏の実際の射として読む。 -/
def dgLastHornFinalClosed :
    ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 2) ⟶
      ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) :=
  (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm (dgLastHornFinalCycle σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
