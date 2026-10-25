module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceArrows
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationEquivalenceLifting

/-!
概要：固定始域の閉包内射圏の包含と終域射影は同値を持ち上げる。
方針：元の脚の全族を使って同型不変性を反映し、全 coslice の公開持ち上げと合成する。
規約：終域射影を left fibration とする主張はしない。
使われ方：固定始域での全図式の相対持ち上げと accessibility の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域の閉包内射への制限は、元の全 coslice 内の同型で不変。 -/
lemma generatedSourceCondition_iff_vertexIso (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    {a b : (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌} (e : VertexIso a b) :
    (JoinCocone.leg a (𝟙 Δ[0])).edge ∈ generatedEdges edges ↔
      (JoinCocone.leg b (𝟙 Δ[0])).edge ∈ generatedEdges edges := by
  have h := generatedArrow_mem_iff_vertexIso edges (VertexIso.map e (sourceCosliceArrowFamily x))
  change arrowVertexEdge ((sourceCosliceArrowFamily x).app _ a) ∈ generatedEdges edges ↔
    arrowVertexEdge ((sourceCosliceArrowFamily x).app _ b) ∈ generatedEdges edges at h
  rw [sourceCosliceArrowFamily_vertex x a, sourceCosliceArrowFamily_vertex x b] at h
  exact h

/-- 固定始域圏の元の全部分包含は同値を持ち上げる。 -/
lemma generatedSourceInclusion_equivalenceLifting (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    F1B.EquivalenceLifting (generatedSourceInclusion edges x) :=
  kanEquivalenceLifting_fullSubcomplexOnVertices_ι _
    (fun e ↦ generatedSourceCondition_iff_vertexIso edges x e)

/-- 固定始域圏の元の終域射影も同値を持ち上げる。 -/
lemma generatedSourceTarget_equivalenceLifting (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    F1B.EquivalenceLifting (generatedSourceTarget edges x) := by
  intro A B i hi he
  have := generatedSourceInclusion_equivalenceLifting edges x i hi he
  have := leftFibration_equivalenceLifting (sliceUnderProjection (SSet.yonedaEquiv.symm x))
    i hi he
  change HasLiftingProperty i
    (generatedSourceInclusion edges x ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x))
  infer_instance

/-- 同じ元の終域射影の inner fibration 性。 -/
lemma generatedSourceTarget_innerFibration (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    InnerFibration (generatedSourceTarget edges x) :=
  F1B.EquivalenceLifting.innerFibration (generatedSourceTarget_equivalenceLifting edges x)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
