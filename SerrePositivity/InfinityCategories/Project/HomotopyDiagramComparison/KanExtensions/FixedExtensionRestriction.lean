module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEndpointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：底と初期図式を固定する延長の空間を、初期図式を通る形状の射で制限する。
方針：相対関手の前合成を、同じ初期図式の fiber へ持ち上げる。
規約：元の全族と終点評価を厳密に保持する。使われ方：三角形から共通長辺への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {K L D E B : SSet.{u}} (p : E ⟶ B) (β : K ⟶ B)
  (k : L ⟶ K) (j : D ⟶ L) (v : D ⟶ E) (hv : v ≫ p = (j ≫ k) ≫ β)

/-- 初期値を同じまま、形状 k に沿って延長の全空間を制限する。 -/
def fixedExtensionRestriction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β (j ≫ k) v hv ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p (k ≫ β) j v (hv.trans (Category.assoc _ _ _)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β k) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι_pre]
      rfl)

/-- 制限後の包含は、元の全族を通常の相対前合成で制限したもの。 -/
lemma fixedExtensionRestriction_ι :
    fixedExtensionRestriction p β k j v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p (k ≫ β) j v (hv.trans (Category.assoc _ _ _)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β k :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 具体的な延長を表す頂点の制限は、同じ実際の図式の前合成である。 -/
lemma fixedExtensionRestriction_vertex (W : K ⟶ E) (hW : W ≫ p = β)
    (hWi : (j ≫ k) ≫ W = v) :
    (fixedExtensionRestriction p β k j v hv).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p β (j ≫ k) v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p (k ≫ β) j v (hv.trans (Category.assoc _ _ _))
        ⟨k ≫ W, by rw [Category.assoc, hW], by rw [← Category.assoc, hWi]⟩ := by
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex p β k W hW

/-- 任意のパラメータの制限族は、元の同じ族を形状 k に沿って制限した射そのもの。 -/
lemma fixedExtensionRestriction_uncurry {T : SSet.{u}}
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β (j ≫ k) v hv) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (t ≫ fixedExtensionRestriction p β k j v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p (k ≫ β) j v (hv.trans (Category.assoc _ _ _))) =
      (k ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv) := by
  have h := congrArg (fun z ↦ t ≫ z) (fixedExtensionRestriction_ι p β k j v hv)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry h).trans
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (Category.assoc t
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p β k)).symm).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre _ k))

variable {C : SSet.{u}} (l : C ⟶ L) (b : B _⦋0⦌) (hb : l ≫ (k ≫ β) = SSet.const b)

/-- 制限してから終点を評価しても、元の全延長を同じ終点で評価した射を厳密に回収する。 -/
lemma fixedExtensionRestriction_endpoint :
    fixedExtensionRestriction p β k j v hv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p (k ≫ β) j v (hv.trans (Category.assoc _ _ _)) l b hb =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint p β (j ≫ k) v hv (l ≫ k) b
        ((Category.assoc _ _ _).trans hb) := by
  apply uncurry_injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p β (j ≫ k) v hv
  have hL := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeExtensionFiberEndpoint_uncurry p (k ≫ β) j v
    (hv.trans (Category.assoc _ _ _)) l b hb (fixedExtensionRestriction p β k j v hv)
  have hU := fixedExtensionRestriction_uncurry p β k j v hv (𝟙 S)
  have hR := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeExtensionFiberEndpoint_uncurry p β (j ≫ k) v hv (l ≫ k) b
    ((Category.assoc _ _ _).trans hb) (𝟙 S)
  simp only [Category.id_comp] at hU hR
  refine hL.trans ?_
  calc
    _ = (l ▷ S) ≫ ((k ▷ S) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv)) :=
      congrArg (fun z ↦ (l ▷ S) ≫ z) hU
    _ = ((l ≫ k) ▷ S) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p β (j ≫ k) v hv) := by
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
    _ = _ := hR.symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
