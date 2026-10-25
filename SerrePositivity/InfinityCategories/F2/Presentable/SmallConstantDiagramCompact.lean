module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallRelativeHomAccessible
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteLeftFibrationCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal

/-!
概要：μ-small な形状上の一点定値図式は、元の全関手 ∞ 圏で μ-compact。
方針：恒等 left fibration の小さい全空間と相対 Hom 保存を使い、分類同値と終対象の一意性で移す。
規約：非可算正則 μ と小さい quasicategory 形状を要求する。
使われ方：μ-small な極限関手の filtered 保存の判定。
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

/-- 概要：全空間が μ-small な left fibration の元の対象は μ-compact。
方針：元の全相対 Hom の μ-filtered 保存を大きい共変 Hom の compact 判定へ移す。
規約：置換や生成表示を新たに要求しない。
使われ方：恒等 left fibration と小さい図式上の一点定値図式。 -/
lemma smallLeftFibrationObject_isKappaCompact
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {B : SSet.{u}} [Quasicategory B] (X : LeftFibrationObject B)
    (hX : IsKappaSmall μ X.val.left) :
    Compact.IsKappaCompact.{u, u + 1} μ (coherentNerveVertex X) :=
  leftFibrationObject_isKappaCompact_of_homPreservation X
    (smallRelativeHom_isKappaAccessibleFunctor hμ X.val hX)

/-- 概要：底の恒等射を全空間として持つ元の left fibration 対象。
方針：恒等射の left fibration 性を束縛する。
規約：全空間を底そのものに固定する。
使われ方：一点定値図式の compact 性の模型。 -/
def identityLeftFibrationObject (B : SSet.{u}) : LeftFibrationObject B :=
  ⟨Over.mk (𝟙 B), by
    change LeftFibration (𝟙 B)
    exact ⟨MorphismProperty.of_isIso leftFibrations _⟩⟩

/-- 概要：恒等 left fibration の分類頂点は全関手 ∞ 圏の終対象。
方針：各点の fiber は恒等射の可縮 fiber であり、全自然な評価比較で終対象性を移す。
規約：頂点ごとの同型を全関手同型と誤認せず、終対象の各点判定を使う。
使われ方：一点定値図式との元の全関手圏内の同型。 -/
lemma straightening_identityLeftFibration_isTerminal (B : SSet.{u}) [Quasicategory B] :
    IsTerminalVertex ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (identityLeftFibrationObject B))) := by
  let X := identityLeftFibrationObject B
  let v := (leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌) (coherentNerveVertex X)
  let F := (functorVertexEquiv _ _).symm v
  have hv : functorVertex F = v := (functorVertexEquiv _ _).apply_symm_apply v
  change IsTerminalVertex v
  rw [← hv]
  apply isTerminalVertex_functorVertex_of_pointwise F
  rintro ⟨b⟩
  have ht := spaceInfinityVertex_isTerminal_of_isContractibleKan (leftFibrationFiberObject b X)
    (vertexFiber_isContractibleKan (𝟙 B) b)
  rw [spaceInfinityVertex_eq_coherent, ← leftFibrationInfinityFiberEvaluation_vertex b X] at ht
  have hi := (leftStraighteningInfinityMap_evaluateIso b).app (coherentNerveVertex X)
  change VertexIso ((evaluateFunctorAt (Y := SpaceInfinity.{u}) (ULift.up b)).app _ v)
    ((leftFibrationInfinityFiberEvaluation b).app _ (coherentNerveVertex X)) at hi
  rw [← hv, evaluateFunctorAt_functorVertex] at hi
  exact ht.of_vertexIso hi.symm

/-- 概要：μ-small な小さい quasicategory 上の一点定値図式は μ-compact。
方針：恒等 left fibration の compact 性を分類全同値で移し、二つの終対象を比較する。
規約：元の全関手圏の compact 性を結論する。
使われ方：小さい極限と μ-filtered 余極限の交換。 -/
lemma smallConstantPointDiagram_isKappaCompact
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (B : SSet.{u}) [Quasicategory B] (hB : IsKappaSmall μ B) :
    Compact.IsKappaCompact.{u, u + 1} μ
      (functorVertex (SSet.const pointSpaceVertex :
        (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) := by
  have hc := smallLeftFibrationObject_isKappaCompact hμ (identityLeftFibrationObject B) hB
  have hi := isKappaCompact_image_of_equivalence (leftStraighteningInfinityEquivalence B) _ hc
  have ht := straightening_identityLeftFibration_isTerminal B
  have ht' := isTerminalVertex_functorVertex_of_pointwise
    (SSet.const pointSpaceVertex : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (fun _ ↦ pointSpaceVertex_isTerminalVertex)
  exact (Compact.isKappaCompact_iff_of_iso (terminalVertexIso ht ht')).mp hi

end SerrePositivity.InfinityCategories.F2.Presentable
