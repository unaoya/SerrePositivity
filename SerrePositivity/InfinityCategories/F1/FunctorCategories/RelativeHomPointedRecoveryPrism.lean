module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomPointedRecoveryEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomCoherentNaturality

/-!
概要：pointed 回収を、元の恒等点に始まる実際の unstraightening の普遍 prism で表す。
方針：既存の全変換の持ち上げを同じ恒等点へ制限し、始点と終点を厳密に計算する。
規約：全 coherent 変換空間を保ち、持ち上げを新たに選ばない。
使われ方：pointed 回収を元の coherent 評価の同じ区間族に沿う輸送へ結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 固定点と動く変換を持つ prism の端点は、同じパラメーター付き端点制限となる。 -/
lemma prismEndpoint_fixedPointParameter {E P T : SSet.{u}} (d : E _⦋0⦌)
    (c : P ⟶ T) (i : Fin 2) :
    prismEndpoint i P ≫ lift
      (lift (fst (Δ[1] : SSet.{u}) P) (SSet.const d))
      (snd (Δ[1] : SSet.{u}) P ≫ c) =
      lift (SSet.const d) c ≫ (simplexPrismVertex 1 i E ▷ T) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の unstraightening 恒等点の pointed 成分は、全パラメーターで同じ恒等点。 -/
lemma relativeHomUnstraighteningIdentity_pointedFamily {B : SSet.{u}}
    (q : LeftFibrationObject B) (P : SSet.{u + 1}) :
    (SSet.const (relativeHomUnstraighteningIdentity q).val : P ⟶ _) ≫
      pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation q.val) =
      SSet.const (relativeHomPointedIdentity q) ≫ vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj q)) := by
  calc
    _ = (SSet.const (relativeHomUnstraighteningIdentity q) : P ⟶ _) ≫
        vertexFiberι (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
          (coherentNerveVertex q) ≫
        pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation q.val) := rfl
    _ = (SSet.const (relativeHomUnstraighteningIdentity q) : P ⟶ _) ≫
        (relativeHomUnstraighteningFiberIso q q).hom ≫ vertexFiberι pointedSpaceProjection
          (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj q)) := by
      rw [relativeHomUnstraighteningFiberIso_hom_ι]
    _ = _ := by
      rw [← Category.assoc, SSet.const_comp]
      exact congrArg (fun z ↦ (SSet.const z : P ⟶ _) ≫ vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj q)))
          (relativeHomUnstraighteningIdentity_pointed q)

/-- 全変換の元の持ち上げを、実際の恒等点に制限した同じ pointed prism。 -/
def relativeHomPointedRecoveryPrism {B : SSet.{u}} (a q : LeftFibrationObject B) :
    (Δ[1] : SSet.{u + 1}) ⊗ pinchedHom
      (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶ PointedSpaceInfinity.{u} :=
  lift (lift (fst Δ[1] _) (SSet.const (relativeHomUnstraighteningIdentity q).val))
    (snd Δ[1] _ ≫ pinchedHomToIntervalMappingSpace
      (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val))) ≫
    leftUnstraighteningTransformationFamilyLift (leftFibrationCoherentEvaluation q.val)
      (leftFibrationCoherentEvaluation a.val)

/-- 同じ普遍 prism は、元の pointed 恒等点に厳密に始まる。 -/
lemma relativeHomPointedRecoveryPrism_zero {B : SSet.{u}} (a q : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomPointedRecoveryPrism a q =
      SSet.const (relativeHomPointedIdentity q) ≫ vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation q.val).obj q)) := by
  rw [relativeHomPointedRecoveryPrism, ← Category.assoc, prismEndpoint_fixedPointParameter,
    Category.assoc]
  have h := congrArg (fun k ↦ lift (SSet.const (relativeHomUnstraighteningIdentity q).val)
    (pinchedHomToIntervalMappingSpace
      (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val))) ≫ k)
    (leftUnstraighteningTransformationFamilyLift_start
      (leftFibrationCoherentEvaluation q.val) (leftFibrationCoherentEvaluation a.val))
  refine h.trans ?_
  calc
    _ = SSet.const (relativeHomUnstraighteningIdentity q).val ≫
        pullback.fst pointedSpaceProjection (leftFibrationCoherentEvaluation q.val) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    _ = _ := relativeHomUnstraighteningIdentity_pointedFamily q _

/-- 同じ普遍 prism の終点は、構成済みの pointed 回収の実際の値。 -/
lemma relativeHomPointedRecoveryPrism_one {B : SSet.{u}} (a q : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomPointedRecoveryPrism a q =
      relativeHomCoherentPointedRecovery a q ≫ vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex ((relativeFunctorEnrichedEvaluation a.val).obj q)) := by
  rw [relativeHomPointedRecoveryPrism, ← Category.assoc, prismEndpoint_fixedPointParameter,
    Category.assoc]
  have h := congrArg (fun k ↦ lift (SSet.const (relativeHomUnstraighteningIdentity q).val)
    (pinchedHomToIntervalMappingSpace
      (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val))) ≫ k)
    (leftUnstraighteningMappingSpaceMap_pointed
      (leftFibrationCoherentEvaluation q.val) (leftFibrationCoherentEvaluation a.val)).symm
  refine h.trans ?_
  rw [leftUnstraighteningMappingSpaceMap_uncurry]
  exact (relativeHomCoherentPointedRecovery_ι a q).symm

/-- 固定した始点と動くパラメーターの prism は、その始点の像で厳密に後合成される。 -/
lemma prismFixedPointParameter_projection {E D P T : SSet.{u}} (p : E ⟶ D)
    (d : E _⦋0⦌) (b : D _⦋0⦌) (hd : p.app (Opposite.op ⦋0⦌) d = b) (c : P ⟶ T) :
    lift (lift (fst (Δ[1] : SSet.{u}) P) (SSet.const d)) (snd Δ[1] P ≫ c) ≫
      ((Δ[1] ◁ p) ▷ T) =
      lift (lift (fst (Δ[1] : SSet.{u}) P) (SSet.const b)) (snd Δ[1] P ≫ c) := by
  have h : (SSet.const d : Δ[1] ⊗ P ⟶ E) ≫ p = SSet.const b := by
    rw [SSet.const_comp, hd]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  exact Prod.ext (Prod.ext rfl (congrArg (fun k ↦ k.app n z) h)) rfl

/-- 同じ持ち上げの底は、元の coherent 変換を表現対象で評価した区間族そのもの。 -/
lemma relativeHomPointedRecoveryPrism_projection {B : SSet.{u}}
    (a q : LeftFibrationObject B) :
    relativeHomPointedRecoveryPrism a q ≫ pointedSpaceProjection =
      lift (fst (Δ[1] : SSet.{u + 1}) _)
        (lift (SSet.const (coherentNerveVertex q)) (snd (Δ[1] : SSet.{u + 1}) _)) ≫
          relativeHomCoherentTransformationPrism a q := by
  rw [relativeHomPointedRecoveryPrism, Category.assoc,
    leftUnstraighteningTransformationFamilyLift_projection]
  have h := prismFixedPointParameter_projection
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    (relativeHomUnstraighteningIdentity q).val (coherentNerveVertex q)
    (relativeHomUnstraighteningIdentity_projection q)
    (pinchedHomToIntervalMappingSpace
      (functorVertex (leftFibrationCoherentEvaluation q.val))
      (functorVertex (leftFibrationCoherentEvaluation a.val)))
  calc
    _ = lift (lift (fst (Δ[1] : SSet.{u + 1}) _) (SSet.const (coherentNerveVertex q)))
        (snd Δ[1] _ ≫ pinchedHomToIntervalMappingSpace
          (functorVertex (leftFibrationCoherentEvaluation q.val))
          (functorVertex (leftFibrationCoherentEvaluation a.val))) ≫
        leftUnstraighteningTransformationFamily (leftFibrationCoherentEvaluation q.val)
          (leftFibrationCoherentEvaluation a.val) :=
      congrArg (fun k ↦ k ≫ leftUnstraighteningTransformationFamily
        (leftFibrationCoherentEvaluation q.val) (leftFibrationCoherentEvaluation a.val)) h
    _ = _ := by
      rw [relativeHomCoherentTransformationPrism, coherentTransformationFamilyDiagram,
        ← leftUnstraighteningTransformationFamily_parameter]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      rfl

end SerrePositivity.InfinityCategories
