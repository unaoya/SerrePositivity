module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentOppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-!
概要：coherent nerve の反対同型が元の通常の辺を反対射の辺へ送ることを照合する。
方針：辺の対象と射を回収し、反対豊穣圏の Hom 同値を計算する。
規約：元の辺を保持する。使われ方：初期外側ホーンの反転による充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 反対圏の後合成は、元の圏の同じ射による前合成である。 -/
lemma eHomWhiskerLeft_op_eq_right {X Y : C} (f : X ⟶ Y) (A : C) :
    eHomWhiskerLeft SSet (Opposite.op A) f.op = eHomWhiskerRight SSet f A := by
  unfold eHomWhiskerLeft eHomWhiskerRight
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- coherent nerve の反対比較は、元の辺を同じ通常の射の反対の辺へ送る。 -/
lemma coherentNerveOppositeMap_edge {X Y : C} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C).app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f.op).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv Cᵒᵖ).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap C).app (Opposite.op ⦋1⦌)
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f.op).edge
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]
  change (⟨Opposite.op Y, Opposite.op X, _⟩ : Σ A B : Cᵒᵖ, A ⟶ B) =
    ⟨Opposite.op Y, Opposite.op X, f.op⟩
  apply congrArg (fun h : Opposite.op Y ⟶ Opposite.op X ↦
    (⟨Opposite.op Y, Opposite.op X, h⟩ : Σ A B : Cᵒᵖ, A ⟶ B))
  apply (SimplicialCategory.homEquiv' (Opposite.op Y) (Opposite.op X)).injective
  change (SimplicialCategory.homEquiv' (Opposite.op Y) (Opposite.op X))
    ((SimplicialCategory.homEquiv' (Opposite.op Y) (Opposite.op X)).symm _) = _
  rw [Equiv.apply_symm_apply]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0 = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  rfl

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
