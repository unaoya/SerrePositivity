module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionCurry
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedStrictConeFamily

/-!
概要：相対延長空間での終点評価を、同じ raw な族の終点での制限と照合する。
方針：定値 fiber への内部 Hom の評価を展開し、前合成・底の同定・curry の往復を計算する。
規約：頂点や同型類だけでなく、任意の全パラメータでの円柱の射を保つ。
使われ方：指定輸送比較の円柱と、延長空間の辺の終点での像との厳密な接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 定値な底の相対関手を fiber へ移して評価しても、元の全パラメータ族を保持する。 -/
lemma relativeFunctorConstFiberHom_uncurry {A L E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌)
    (t : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p (SSet.const b : A ⟶ B)) :
    uncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom p b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry t := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom]
  rw [uncurry_natural_left, uncurry_curry, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, Category.comp_id]

/-- 相対延長の終点評価を展開すると、同じ族を指定した終点へ制限した射になる。 -/
lemma relativeExtensionFiberEndpoint_uncurry {A D C L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)
    (t : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β i v hv) :
    uncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β i v hv j b hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      (j ▷ L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β i v hv) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint]
  simp only [← Category.assoc]
  rw [relativeFunctorConstFiberHom_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.relativeFunctorUncurry_eqToHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre]
  exact hj

/-- 元の raw な族を戻した後の終点評価も、同じ族の制限を厳密に回収する。 -/
lemma fixedExtensionCurry_endpoint_uncurry {A D C L E B : SSet.{u}}
    (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ β)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)
    (W : A ⊗ L ⟶ E) (hW : W ≫ p = fst A L ≫ β)
    (hI : (i ▷ L) ≫ W = fst D L ≫ v) :
    uncurry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry p β i v hv W hW hI ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β i v hv j b hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = (j ▷ L) ≫ W := by
  rw [relativeExtensionFiberEndpoint_uncurry, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionCurry_uncurry]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
