module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGFourLastHornCochains
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom

/-! # 実四次最後外ホーンの最後の閉辺

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
variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 実ホーンの既知データの最後の次数零辺は閉じている。 -/
lemma dgFourLastHornFinalEdge_closed :
    _root_.SerrePositivity.DifferentialGraded.differential A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide)) = 0 := by
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_equation σ {3, 4} 3 4 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine hd.trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj : j.val = (3 : Fin 5) ∨ j.val = 4 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using j.property
  rcases hj with h | h
  · simp [h]
  · simp [h]

/-- 最後の辺を、二未知式で使う元の Hom 複体の閉零 cycle として読む。 -/
def dgFourLastHornFinalCycle : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide), dgFourLastHornFinalEdge_closed σ⟩

/-- 最後の辺を、元の閉零 dg 圏の実際の射として読む。 -/
def dgFourLastHornFinalClosed :
    ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) ⟶
      ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4) :=
  (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm (dgFourLastHornFinalCycle σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
