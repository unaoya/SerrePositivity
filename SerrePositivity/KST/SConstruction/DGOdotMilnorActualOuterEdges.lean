module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorActualSRectangle
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEdgeDiagram
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero

/-!
概要：共通実長方形の外周の四辺と元零角を厳密に回収する。
方針：転置した元貼合せの二外辺と上下元合成二単体の中間面を使う。
規約：元 cell 始域・元中央射と実差の厳密合成・元 V の全対象商を保持する。
使われ方：実外周の全図式認証と元 resolved 射影の指定境界。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma outerBottom {X : SSet.{v}} (D : (Δ[2] ⊗ Δ[1] : SSet.{v}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 2) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_leftEdge D).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_bottom _).symm)
private lemma outerTop {X : SSet.{v}} (D : (Δ[2] ⊗ Δ[1] : SSet.{v}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 0) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top _).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_outer_rightEdge D).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_top _).symm)
private lemma outerLeft {X : SSet.{v}} (D : (Δ[2] ⊗ Δ[1] : SSet.{v}) ⟶ X)
    {x y z : X _⦋0⦌} {a : X.Edge x y} {b : X.Edge y z} {c : X.Edge x z}
    (t : SSet.Edge.CompStruct a b c)
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle D = SSet.yonedaEquiv.symm t.simplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 1) =
      SSet.yonedaEquiv.symm c.edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_left _).trans ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_bottomEdge D 1).trans
    ((congrArg (fun f => stdSimplex.δ (1 : Fin 3) ≫ f) h).trans t.δ_one_yonedaEquiv_symm))
private lemma outerRight {X : SSet.{v}} (D : (Δ[2] ⊗ Δ[1] : SSet.{v}) ⟶ X)
    {x y z : X _⦋0⦌} {a : X.Edge x y} {b : X.Edge y z} {c : X.Edge x z}
    (t : SSet.Edge.CompStruct a b c)
    (h : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingTopTriangle D = SSet.yonedaEquiv.symm t.simplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((β_ (Δ[1] : SSet.{v}) Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare D 1) =
      SSet.yonedaEquiv.symm c.edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.square_transpose_right _).trans ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_topEdge D 1).trans
    ((congrArg (fun f => stdSimplex.δ (1 : Fin 3) ≫ f) h).trans t.δ_one_yonedaEquiv_symm))
private lemma zeroVertex {X : SSet.{v}} (F : (Δ[1] ⊗ Δ[1] : SSet.{v}) ⟶ X)
    {x z : X _⦋0⦌} (a : X.Edge x z)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ F = SSet.yonedaEquiv.symm a.edge) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1 = z := by
  have hv := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target F
  rw [h, Equiv.apply_symm_apply, a.tgt_eq] at hv
  exact hv.symm

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "U" => DGOdotMilnorRightAxisBase R d
local notation "O" => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.verdierRectangleFace 1 ≫ dgOdotMilnorActualRectangleDiagram R d
local notation "VInput" => dgIdentityHomGluingNullInput R (U)

/-- 概要：同じ実外周の四辺は元核包含・元厳密合成・元零辺そのもの。
方針：元上下合成二単体の中間辺と元二外辺を回収する。
規約：元四つの全一単体を保持。使われ方：外周の指定境界。 -/
lemma dgOdotMilnorActualOuter_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (O) = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorFlatKernelInputMap R d)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (O) = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorRightAxisInputMap R d ≫
          dgIdentityHomGluingDifferenceInputMap R (U))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ (O) = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d ≫
          dgFixedNullLeft R (A := VInput))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ (O) = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgIdentityHomGluingNullContracted R (U)))).edge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (outerBottom (dgOdotMilnorActualRectangleDiagram R d)).trans
      ((congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ f)
        (dgOdotMilnorActualRectangleDiagram_comparison R d)).trans
          (dgOdotMilnorKernelActualComparisonSquare_edges R d).1)
  · exact outerRight (dgOdotMilnorActualRectangleDiagram R d)
      (dgOdotMilnorActualRectangleTopTriangle R d) (dgOdotMilnorActualRectangleDiagram_top R d)
  · exact outerLeft (dgOdotMilnorActualRectangleDiagram R d)
      (dgOdotMilnorActualRectangleBottomTriangle R d)
      (dgOdotMilnorActualRectangleDiagram_bottom R d)
  · exact (outerTop (dgOdotMilnorActualRectangleDiagram R d)).trans
      ((congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ f) (dgOdotMilnorActualRectangleDiagram_right R d)).trans
        (dgIdentityHomGluingNullDomainSquare_edges R (U)).2.2.2)

/-- 概要：実外周の元零角は同じ V の全対象商。
方針：元左合成辺の終点を回収する。
規約：元頂点の厳密等号。使われ方：外周の固定 ν 零角条件。 -/
lemma dgOdotMilnorActualOuter_zero_vertex :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (O) 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgFixedNullInput R (VInput)) :=
  zeroVertex (O) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorKernelNullFactorInputMap R d ≫
    dgFixedNullLeft R (A := VInput))) (dgOdotMilnorActualOuter_edges R d).2.2.1

/-- 概要：同じ実外周の固定 ν 零角は零 Cat^perf 圏。
方針：元全対象商に Sp 正本の零性を適用する。
規約：元 V 零角を保持。使われ方：外周の零対角を使う全比較。 -/
lemma dgOdotMilnorActualOuter_perfect_zero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex ((O) ≫ dgKInputPerfectNu R) 0 1)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (O) 0 1)))
  rw [dgOdotMilnorActualOuter_zero_vertex, dgKInputPerfectNu_vertex]
  exact dgFixedNullInput_isZeroCategory R (VInput)

end SerrePositivity.KST.SConstruction
