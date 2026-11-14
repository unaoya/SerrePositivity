module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointTarget
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagramFibers
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberRotation
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

lemma inverseRotation_source_zero (a : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X) _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex a) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((inverseRotation X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) a) := by
  let z := (rightSection X).app (Opposite.op ⦋0⦌) a
  have hz : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X).app (Opposite.op ⦋0⦌) z = a := by
    exact congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.arrows X => f.app (Opposite.op ⦋0⦌) a)
      (rightSection_right X)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge a =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram z.val)).edge := by
    rw [← hz, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiber_diagram_right_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram z.val)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp ha
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) z)
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiber_diagram_bottom_source]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zero_source_of_right_invertible X z hi

end SerrePositivity.KST.LocalizingInvariants.CofiberRotation
