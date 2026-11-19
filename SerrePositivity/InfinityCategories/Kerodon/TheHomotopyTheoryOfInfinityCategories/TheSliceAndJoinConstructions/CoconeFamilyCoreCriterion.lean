module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyCoreCriterion

public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinPrismFixed

/-!
概要：余錐全族の前段と頂点の辺反転から、その同じ全族の辺反転を証明する。
方針：指定されたパラメータ辺を全図式頂点で検査し、join の二因子で尽くす。
規約：パラメータやその区間に Kan 性を仮定せず、元の実全族を変更しない。
使われ方：実分母円柱の商像を元の全図式 core へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 前段の全辺と固定頂点が与える、同じ全余錐族の全パラメータ辺の反転。 -/
lemma coconeFamily_invertsAllEdges_of_prefix_apex {P L X : SSet.{u}} [Quasicategory X]
    (F : P ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (Δ[0] : SSet.{u}))).obj X) (z : X _⦋0⦌)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L Δ[0])).app X) Set.univ)
    (hz : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.functorFamily_invertsEdges_of_evaluations
  intro v
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertex_cases L Δ[0] v with ⟨l, rfl⟩ | ⟨b, rfl⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl L Δ[0]) l, ← Category.assoc]
    intro s hs
    exact (hp hs).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l)
  · have hb : b = stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
      apply stdSimplex.obj₀Equiv.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.eq_zero _
    subst b
    rw [hz]
    exact invertsEdges_const _ _ _ Set.univ

end SerrePositivity.KST.LocalizingInvariants
