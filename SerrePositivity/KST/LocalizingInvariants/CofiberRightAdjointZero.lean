module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointTarget
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagramFibers

/-!
概要：cofiber の実右随伴の矢印は始点が零で、終点は元の入力である。
方針：恒等矢印の右辺を持つ元の cofiber 四角形を fiber として読む。
規約：同じ右辺切断と同じ関手を保持。使われ方：Cone の右随伴の零始点表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 恒等矢印を右辺として持つ、元の逆回転で選んだ cofiber 四角形。 -/
def cofiberRightAdjointDiagram (x : X _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X) _⦋0⦌ :=
  (CofiberRotation.rightSection X).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow X).app (Opposite.op ⦋0⦌) x)

lemma cofiberRightAdjointDiagram_right (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (cofiberRightAdjointDiagram X x).val = SSet.const x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiber_diagram_right_vertex]
  have h := congrArg (fun f : (ihom (Δ[1] : SSet.{u})).obj X ⟶ _ =>
    f.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow X).app (Opposite.op ⦋0⦌) x))
    (CofiberRotation.rightSection_right X)
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right X).app (Opposite.op ⦋0⦌)
    (cofiberRightAdjointDiagram X x) = (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.identityArrow X).app (Opposite.op ⦋0⦌) x at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex Δ[1] x)

lemma cofiberRightAdjointDiagram_right_invertible (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (cofiberRightAdjointDiagram X x).val)) := by
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := e)
    (f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (cofiberRightAdjointDiagram X x).val)) ?_).1 hi
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, cofiberRightAdjointDiagram_right]
  have hc : SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 := rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x).symm.trans hc.symm

/-- 元の cofiber の右随伴は各入力を零始点の矢印へ送る。 -/
lemma cofiberRightAdjoint_source_zero (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((cofiberRightAdjoint X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) x) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌)
      (cofiberRightAdjointDiagram X x))
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiber_diagram_bottom_source]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zero_source_of_right_invertible X (cofiberRightAdjointDiagram X x)
    (cofiberRightAdjointDiagram_right_invertible X x)

end SerrePositivity.KST.LocalizingInvariants
