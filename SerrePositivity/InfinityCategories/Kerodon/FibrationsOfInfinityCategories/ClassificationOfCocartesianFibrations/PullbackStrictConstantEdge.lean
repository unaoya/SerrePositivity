module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackStrictEvaluation
public import SerrePositivity.KST.Fibration.ConstantFiberPrism
public import SerrePositivity.KST.Fibration.CocartesianKanDiagram

/-! # 底で定値となる辺に沿う元の strict section 輸送の局所化可逆性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の底の辺が定値なら、同じ fiber 内の評価 prism で strict transport の可逆性を検出する。 -/
theorem pullbackStrictTransportMap_constantEdge_localized_isIso
    {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd q k)]
    {c d : I} (f : c ⟶ d) (b : B _⦋0⦌)
    (hc : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = b)
    (hd : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) = b)
    (hf : yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k = SSet.const b) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap (pullback.snd q k) f)) := by
  let u := pullbackStrictEvaluationAt q k c b hc
  let v := pullbackStrictEvaluationAt q k d b hd
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportMap (pullback.snd q k) f
  let H := strictTransportEvaluationPrism (pullback.snd q k) f ≫ pullback.fst q k
  have hp : H ≫ q = SSet.const b := by
    dsimp only [H]
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      strictTransportEvaluationPrism_projection, Category.assoc, hf, SSet.comp_const]
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b := by
    dsimp only [H]
    rw [← Category.assoc, strictTransportEvaluationPrism_zero, Category.assoc]
    exact (pullbackStrictEvaluationAt_ι q k c b hc).symm
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = (t ≫ v) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b := by
    dsimp only [H]
    rw [← Category.assoc, strictTransportEvaluationPrism_one, Category.assoc, Category.assoc]
    exact (congrArg (fun m => t ≫ m) (pullbackStrictEvaluationAt_ι q k d b hd).symm).trans
      (Category.assoc _ _ _).symm
  have he := constantFiberPrism_localized_eq q b u (t ≫ v) H h₀ h₁ hp
  have hu := pullbackStrictEvaluationAt_localized_isIso q k c b hc
  have hv : IsIso (AnodyneHomotopy.anodyneQ.map v) :=
    pullbackStrictEvaluationAt_localized_isIso q k d b hd
  have ht : IsIso (AnodyneHomotopy.anodyneQ.map t ≫ AnodyneHomotopy.anodyneQ.map v) := by
    rw [← Functor.map_comp, ← he]
    exact hu
  exact (isIso_comp_right_iff _ _).mp ht

/-- 同じ厳密 Kan 図式の遷移も、底で定値となる辺を実際の同値に送る。 -/
theorem cocartesianKanDiagram_map_constantEdge_isQCatEquivalence
    {I : Type u} [Category.{u} I] {F B : SSet.{u}}
    (q : F ⟶ B) (k : nerve I ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.snd q k)]
    {c d : I} (f : c ⟶ d) (b : B _⦋0⦌)
    (hc : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) = b)
    (hd : k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex d) = b)
    (hf : yonedaEquiv.symm (nerve.edgeMk f).edge ≫ k = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((cocartesianKanDiagram (pullback.snd q k)).map f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion_map_isQCatEquivalence _
    (pullbackStrictTransportMap_constantEdge_localized_isIso q k f b hc hd hf)

end SerrePositivity.KST.Fibration
