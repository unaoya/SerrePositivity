module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTopChain
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveTransportPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantNaturality

/-!
概要：最大添字を持つ weighted 全空間を、その添字での評価へ輸送する全円柱。
方針：底の射列と全初区間の係数を同じ時刻で最大添字へ送る。
規約：係数の可逆性は不要。使われ方：小さい weighted 図式の一段への輸送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [PartialOrder I] [OrderTop I] (F : I ⥤ SSet.{u})

/-- 元の weighted 全図式の、最大添字への同時輸送の円柱。 -/
def weightedTopPrism : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F where
  app d := ↾fun ⟨t, s⟩ =>
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTopChain s.1 (stdSimplex.objEquiv t).toOrderHom,
      s.2 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedTopChainCoefficient F s.1 (stdSimplex.objEquiv t).toOrderHom⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, s⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext j
    change (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop j) ≫
        s.2.app (α.unop.toOrderHom j)) ≫ F.map _ =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop j) ≫
        (s.2.app (α.unop.toOrderHom j) ≫ F.map _)
    exact Category.assoc _ _ _

/-- 同時輸送の始端は、元の全 weighted 図式の恒等射。 -/
lemma weightedTopPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ≫ weightedTopPrism F = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n at s
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change s.2.app j ≫ F.map (homOfLE (show s.1.obj j ≤ s.1.obj j from le_rfl)) = s.2.app j
  have h : (homOfLE (show s.1.obj j ≤ s.1.obj j from le_rfl)) = 𝟙 (s.1.obj j) :=
    Subsingleton.elim _ _
  rw [h, F.map_id]
  exact Category.comp_id (s.2.app j)

/-- 同時輸送の終端は、最大添字での元の評価と同じ係数包含の合成。 -/
lemma weightedTopPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) ≫ weightedTopPrism F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveTerminalEvaluation F (Limits.isTerminalTop : Limits.IsTerminal (⊤ : I)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F ⊤ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n at s
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext j
  change s.2.app j ≫ F.map (homOfLE (show s.1.obj j ≤ ⊤ from le_top)) =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (s.2.app (Fin.last n) ≫ F.map (homOfLE (show s.1.obj (Fin.last n) ≤ ⊤ from le_top))))
  have ht : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n _) ≫ s.2.app (Fin.last n) =
      s.2.app j ≫ F.map (s.1.map (homOfLE (Fin.le_last j))) :=
    s.2.naturality (homOfLE (Fin.le_last j))
  rw [Equiv.symm_apply_apply, ← Category.assoc, ht,
    Category.assoc, ← F.map_comp]
  exact congrArg (fun f => s.2.app j ≫ F.map f) (Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
