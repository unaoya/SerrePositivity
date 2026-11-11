module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：通常の射の豊穣表示の一致を、同じ coherent な辺の像の厳密な一致へ移す。
方針：一単体の射データの同値と、零単体での元の豊穣作用を使う。
規約：同型の類ではなく、元の辺の一単体そのものを保持する。
使われ方：元の底変換結合同型の分類像と既存の coherent 比較を結ぶ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 元の通常の射の豊穣表示を保つ場合、同じ coherent な辺の像も厳密に一致する。 -/
lemma coherentNerveMap_edge_of_homEquiv
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {X Y : C} (f : X ⟶ Y)
    (g : F.obj X ⟶ F.obj Y) (h : eHomEquiv SSet.{u} f ≫ F.map X Y = eHomEquiv SSet.{u} g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv D).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ g))
  refine Eq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow g).symm
  have h₀ : (F.map X Y).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' X Y f) =
      SimplicialCategory.homEquiv' (F.obj X) (F.obj Y) g :=
    congrArg (SSet.unitHomEquiv _) h
  change (⟨F.obj X, F.obj Y, (SimplicialCategory.homEquiv' _ _).symm
    ((F.map X Y).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0))⟩ :
        Σ A B : D, A ⟶ B) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, h₀, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
