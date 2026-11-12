module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveEnriched

/-!
概要：weighted nerve の全 Hom 作用は、パラメーター付き係数の可換式を保つ。
方針：各初区間での全評価の式を取り出し、係数の可換式をそのまま前合成する。
規約：頂点だけではなく元の全パラメーターを保持する。
使われ方：native な反転係数作用を元の weighted Hom 作用と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 全 Hom の weighted 作用の各係数は、初区間に制限した同じパラメーターの評価。 -/
lemma weightedNerveMappingFamily_parameter_component {I : Type u} [SmallCategory I]
    (F G : I ⥤ SSet.{u}) {H : SSet.{u}} (r : H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) (h : H _⦋n⦌) (j : Fin (n + 1)) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily F G).app (Opposite.op ⦋n⦌)
      (s, r.app _ h)).2).app j =
    lift (s.2.app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
        SSet.yonedaEquiv.symm h) ≫
      uncurry (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (s.1.obj j)) := by
  let a := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
    SSet.yonedaEquiv.symm h
  change lift (s.2.app j) (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫
    SSet.yonedaEquiv.symm (r.app _ h)) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (s.1.obj j)) = _
  rw [← SSet.yonedaEquiv_symm_comp h r]
  have hl : lift (s.2.app j) (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫
      (SSet.yonedaEquiv.symm h ≫ r)) =
    lift (s.2.app j) a ≫ (F.obj (s.1.obj j) ◁ r) :=
    (lift_whiskerLeft (s.2.app j) a r).symm
  rw [hl, Category.assoc, ← uncurry_natural_left]

/-- パラメーター付き係数作用の厳密な可換式は、weighted nerve の全作用の可換式を与える。 -/
lemma weightedNerveMappingFamily_intertwine {I : Type u} [SmallCategory I]
    (F G F' G' : I ⥤ SSet.{u}) {H : SSet.{u}}
    (r : H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G) (r' : H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F' G')
    (a : F ⟶ F') (b : G ⟶ G')
    (hab : ∀ i, uncurry (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G i) ≫ b.app i =
      (a.app i ▷ H) ≫ uncurry (r' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F' G' i)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ◁ r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily F G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap b =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap a ▷ H) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F' ◁ r') ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily F' G' := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ, τ⟩, h⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily F G).app (Opposite.op ⦋n⦌)
      (⟨σ, τ⟩, r.app _ h)).2).app j ≫ b.app (σ.obj j) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily F' G').app (Opposite.op ⦋n⦌)
      (⟨σ, τ ≫ Functor.whiskerLeft σ a⟩, r'.app _ h)).2).app j
  rw [weightedNerveMappingFamily_parameter_component F G r ⟨σ, τ⟩ h j,
    weightedNerveMappingFamily_parameter_component F' G' r'
      ⟨σ, τ ≫ Functor.whiskerLeft σ a⟩ h j, Category.assoc, hab]
  rw [← Category.assoc, lift_whiskerRight]
  rfl

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
