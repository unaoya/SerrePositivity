module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.F2.Compact.TerminalApexColimit
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation
public import SerrePositivity.InfinityCategories.F2.Compact.FilteredUniverse
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：恒等 left fibration の全分類図式は filtered 余極限を保存する。
方針：実際の fiber 評価との同型で各値を終対象と判定する。
規約：全分類図式を固定し、各点の可縮性から全余錐の普遍性を示す。
使われ方：coslice の Hom の対角引き戻しに現れる一点分類の保存性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：恒等 left fibration の分類の各値は終対象。
方針：同じ fiber 評価との全自然比較と恒等射の可縮 fiber を使う。
規約：元の分類関手の指定した値を保持する。
使われ方：一点分類の filtered 余極限保存。 -/
lemma identityClassification_value_isTerminal {B : SSet.{u}} [Quasicategory B]
    (b : B _⦋0⦌) :
    IsTerminalVertex ((leftStraighteningInfinityDiagram (𝟙 B)).app
      (Opposite.op ⦋0⦌) (ULift.up b)) := by
  let X := leftFibrationObjectOf (𝟙 B)
  have ht := spaceInfinityVertex_isTerminal_of_isContractibleKan (leftFibrationFiberObject b X)
    (vertexFiber_isContractibleKan (𝟙 B) b)
  rw [spaceInfinityVertex_eq_coherent, ← leftFibrationInfinityFiberEvaluation_vertex b X] at ht
  have hi := (leftStraighteningInfinityMap_evaluateIso b).app (leftFibrationInfinityVertex (𝟙 B))
  change VertexIso ((evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)).app _
    ((leftStraighteningInfinityMap B).app _ (leftFibrationInfinityVertex (𝟙 B))))
    ((leftFibrationInfinityFiberEvaluation b).app _ (leftFibrationInfinityVertex (𝟙 B))) at hi
  rw [← leftStraighteningInfinityDiagram_vertex, evaluateFunctorAt_functorVertex] at hi
  exact ht.of_vertexIso hi.symm

/-- 概要：恒等 left fibration の全分類図式は小さい κ-filtered 余極限を保存する。
方針：元の各値と余錐頂点の終対象性から、同じ全余錐を余極限と判定する。
規約：κ には無限性だけを要求する。
使われ方：固定始域 coslice の compact 性の対角引き戻し判定。 -/
lemma identityClassification_preservesKappaFilteredColimits
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (B : SSet.{u + 1}) [Quasicategory B] :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      (leftStraighteningInfinityDiagram (𝟙 B)) := by
  intro I hI hIf D c _hc
  have : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hκ I
  have : IsFilteredInfinity ((SSet.uliftFunctor.{u + 1, u}).obj I) :=
    Compact.isFilteredInfinity_ulift I
  apply Compact.isColimitCone_of_terminal_values
    ((SSet.uliftFunctor.{u + 2, u + 1}).map D ≫ leftStraighteningInfinityDiagram (𝟙 B))
  · rintro ⟨i⟩
    exact identityClassification_value_isTerminal (D.app _ (ULift.up i))
  · rw [Ind.mapJoinCocone_vertex, JoinCocone.ulift_vertex]
    exact identityClassification_value_isTerminal c.vertex

end SerrePositivity.InfinityCategories.F2.Presentable
