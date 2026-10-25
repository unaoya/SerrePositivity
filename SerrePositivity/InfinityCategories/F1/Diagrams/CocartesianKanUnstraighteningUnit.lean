module

public import SerrePositivity.InfinityCategories.F1.Diagrams.SmallKanUnstraighteningUnitValue
public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanWeightedFiberRecovery
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestriction

/-!
概要：元の cocartesian fibration から Kan 置換した直値図式の小さい unstraightening への全族単位。
方針：同じ weighted 単位に直値の復元比較を合成し、全 fiber の指定値回収を共通解像で照合する。
規約：元の全空間・厳密な底・元の自然変換・全 fiber の関手同型を同時に保持する。
使われ方：Ind-S (5)、K-B-S の単体圏上の全族単位の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の cocartesian 全族から指定 unstraightening への実射・厳密な底・全 fiber の単位回収。 -/
lemma exists_cocartesianKanUnstraighteningUnit
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    ∃ f : E ⟶ smallLeftUnstraightening
        (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)),
      ∃ hf : f ≫ smallLeftUnstraighteningProjection
          (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) = p,
      ∀ c : I, Nonempty (FunctorIso
        (vertexFiberMap p _ f hf (nerveVertex c) ≫
          (smallLeftUnstraighteningFiberValueEquivalence
            (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) (nerveVertex c)).hom ≫
          R.map (cocartesianStrictTransportEvaluate p c))
        (η.app (vertexFiber p (nerveVertex c)))) := by
  let F := cocartesianStrictTransportDiagram p ⋙ R
  let G := F ⋙ kanObjectForget
  obtain ⟨a, ha, ⟨ea⟩⟩ := exists_cocartesianKanWeightedUnit p R η
  obtain ⟨b, hb, ⟨eb⟩⟩ := exists_kanWeightedUnstraighteningUnit F
  have hf : (a ≫ b) ≫ smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F) = p := by
    rw [Category.assoc, hb, ha]
  refine ⟨a ≫ b, hf, fun c => ?_⟩
  have : ∀ i, KanComplex (G.obj i) := fun i => (F.obj i).isKanComplex
  have hbval : FunctorIso
      (weightedNerveFiberMap G c ≫ vertexFiberMap _ _ b hb (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve F) (nerveVertex c)).hom) (𝟙 (F.obj c).obj) := by
    have h := FunctorIso.postcomp (kanWeightedUnstraighteningUnit_fiber_commonIso F b hb eb c)
      (smallLeftUnstraighteningFiberValueEquivalence
        (kanDiagramCoherentNerve F) (nerveVertex c)).hom
    have h' := h ≪≫ smallReversedWeightedKanUnstraighteningComparison_valueCommonIso F c
    have hr := (isQCatEquivalence_of_trivialKanFibration
      (edgewiseRight (F.obj c).obj)).isPrecompositionEquivalence (F.obj c).obj
    apply hr.isFullyFaithful.preimageVertexIso
    erw [functorVertex_precomposition, functorVertex_precomposition]
    simpa only [Category.assoc, Category.comp_id] using h'
  have hbinv := FunctorIso.precomp hbval (weightedNerveFiberIso G c).inv
  simp only [weightedNerveFiberIso, asIso_inv, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp, Category.comp_id] at hbinv
  have h₁ := FunctorIso.precomp (FunctorIso.postcomp hbinv
    (R.map (cocartesianStrictTransportEvaluate p c)))
    (vertexFiberMap p _ a ha (nerveVertex c))
  obtain ⟨h₂⟩ := cocartesianKanWeightedUnit_fiber_recovery p R η a ha ea c
  have h := h₁ ≪≫ h₂
  simp only [← Category.assoc] at h
  erw [vertexFiberMap_comp p (weightedNerveProjection G)
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F)) a b ha hb] at h
  simpa only [Category.assoc] using Nonempty.intro h

end SerrePositivity.InfinityCategories
