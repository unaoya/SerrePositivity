module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointTarget
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagramFibers
public import SerrePositivity.KST.LocalizingInvariants.EquivalencePathFamily

/-!
概要：可逆な矢印を逆 cofiber 回転すると始点が零になる。
方針：元の右辺切断を保持し、同じ四角形の fiber 判定を使う。
規約：対象ごとの同型で矢印族を置き換えない。使われ方：普遍差への比較の D 上の零化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberRotation
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

lemma inverseRotation_source_zero (a : (arrows X) _⦋0⦌)
    (ha : IsEquivalencePathVertex a) :
    IsZeroVertex ((inverseRotation X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) a) := by
  let z := (rightSection X).app (Opposite.op ⦋0⦌) a
  have hz : (CofiberDiagrams.right X).app (Opposite.op ⦋0⦌) z = a := by
    exact congrArg (fun f : arrows X ⟶ arrows X => f.app (Opposite.op ⦋0⦌) a)
      (rightSection_right X)
  have he : intervalFunctorVertexEdge a =
      (squareRightArrow (squareDiagram z.val)).edge := by
    rw [← hz, _root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiber_diagram_right_vertex, intervalFunctorVertexEdge_functorVertex,
      squareRightArrow_edge]
  have hi : IsInvertibleEdge (squareRightArrow (squareDiagram z.val)) :=
    (isInvertibleEdge_congr he).mp ha
  change IsZeroVertex ((CofiberDiagrams.bottom X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) z)
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiber_diagram_bottom_source]
  exact CofiberDiagrams.zero_source_of_right_invertible X z hi

end SerrePositivity.KST.LocalizingInvariants.CofiberRotation
