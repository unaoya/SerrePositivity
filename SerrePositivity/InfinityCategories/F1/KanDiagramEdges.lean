module

public import SerrePositivity.InfinityCategories.F1.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.CoherentEdgeEquiv
public import SerrePositivity.InfinityCategories.F1.UniverseInvertibleEdge

/-!
概要：strict な Kan 値図式の coherent 表示における一単体の計算。
方針：coherent な一単体の端点付き射データを比較する。
規約：零単体の表示の差を避け、一単体そのものの等式を先に述べる。
使われ方：Kerodon Remark 3.1.6.3、Corollary 5.6.0.6、普遍射影の輸送を空間の射に沿って計算する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式の射の一単体の像は、その係数の射の coherent な辺の一単体。
方針：一単体と端点付き射データの同値の単射性で比較する。
規約：左辺の底の一単体は宇宙持ち上げする。
使われ方：Kerodon Remark 3.1.6.3、Corollary 5.6.0.6、普遍射影の辺の具体的な表示。 -/
lemma kanDiagramCoherentNerve_edge
    {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) {c d : C} (f : c ⟶ d) :
    (kanDiagramCoherentNerve F).app (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge) =
      (coherentNerveEdge (F.map f)).edge := by
  apply (coherentNerveArrowDataEquiv KanObject.{u}).injective
  change coherentNerveArrowData _ = coherentNerveArrowData _
  rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow]
  change (⟨F.obj c, F.obj d, (SimplicialCategory.homEquiv' _ _).symm
    (PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) 0)⟩ :
      Σ X Y : KanObject.{u}, X ⟶ Y) = _
  rw [pinchedConstant_zero, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories
