module

public import SerrePositivity.InfinityCategories.F1.CoherentHomComparisonVertices
public import SerrePositivity.InfinityCategories.F1.PointedReverseFiberCoordinates
public import SerrePositivity.InfinityCategories.F1.CosliceFiberVertices

/-!
概要：左 coslice fiber 比較の零単体を、元の射の coherent な辺として同定する。
方針：元の錐の値を取り出し、二点 join の標準同型と左 Hom の零単体計算を使う。
規約：反転した Hom の零単体を明示して入力する。
使われ方：pointed fiber の点と実際の一点 Hom 係数の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 左 coslice 比較の零単体が表す辺は、元の豊穣零単体の通常の射の辺そのもの。 -/
lemma coherentCosliceFiberComparison_vertex_edge
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y : C)
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    cosliceFiberVertexToEdge
      ((HomotopyLimits.coherentCosliceFiberComparison X Y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm s))) =
      coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s) := by
  apply SSet.Edge.ext
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((HomotopyLimits.coherentCosliceFiberComparison X Y).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm s))).val.val) = _
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((pinchedLeftCosliceFiberIso (coherentNerveVertex X) (coherentNerveVertex Y)).hom.app
      (Opposite.op ⦋0⦌) ((HomotopyLimits.coherentLeftHomComparison X Y).app
        (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm s)))).val.val) = _
  rw [pinchedLeftCosliceFiberIso_app_val]
  have hi : (leftPointStdSimplexIso.{max u v} 0).hom =
      (joinStdSimplexIso 0 0).hom := rfl
  rw [hi, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply,
    HomotopyLimits.coherentLeftHomComparison_simplex]
  exact coherentLeftHomComparisonSimplex_zero_edge s

end SerrePositivity.InfinityCategories
