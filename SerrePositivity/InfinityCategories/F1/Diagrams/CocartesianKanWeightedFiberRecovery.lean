module

public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanWeightedUnit
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorFiberHom

/-!
概要：底を固定した全族単位の相対回収から、全 fiber 上の元の Kan 単位を回収する。
方針：scaffold の fiber 同型で制限し、恒等射評価の前合成同値で同型を反映する。
規約：元の全空間・指定自然変換・全 fiber を同時に保持する。
使われ方：Ind-S (5) の weighted nerve 段階の全族回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 同じ scaffold の単位の fiber 制限は、元の自然変換の成分そのもの。 -/
lemma cocartesianKanWeightedScaffoldUnit_fiber {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) (R : SSet.{u} ⥤ KanObject.{u})
    (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) (c : I) :
    simplicialReplacementFiberMap (cocartesianStrictTransportDiagram p) c ≫
      vertexFiberMap _ _ (cocartesianKanWeightedScaffoldUnit p R η)
        (cocartesianKanWeightedScaffoldUnit_projection p R η) (nerveVertex c) =
      η.app ((cocartesianStrictTransportDiagram p).obj c) ≫
        weightedNerveFiberMap ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) c := by
  apply vertexFiber_hom_ext
  change simplicialReplacementConstantLift (cocartesianStrictTransportDiagram p) c ≫
    (tautScaffold _ ≫ weightedNerveMap _) = _
  rw [← Category.assoc, simplicialReplacementConstantLift_tautScaffold]
  have h := weightedNerveMap_fiber_naturality
    (cocartesianKanWeightedUnitTransformation p R η) c
  exact congrArg (fun k => k ≫ vertexFiberι _ (nerveVertex c)) h

/-- 相対回収を持つ同じ全族写像は、全 fiber 上で元の Kan 単位を回収する。 -/
lemma cocartesianKanWeightedUnit_fiber_recovery {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget)
    (f : E ⟶ weightedNerve ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget))
    (hf : f ≫ weightedNerveProjection
      ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) = p)
    (e : VertexIso
      (relativeFunctorVertex _ (simplicialReplacementProjection
        (cocartesianStrictTransportDiagram p)) (cocartesianUniversalScaffold p ≫ f)
        (by rw [Category.assoc, hf, cocartesianUniversalScaffold_projection]))
      (relativeFunctorVertex _ _ (cocartesianKanWeightedScaffoldUnit p R η)
        (cocartesianKanWeightedScaffoldUnit_projection p R η))) (c : I) :
    Nonempty (FunctorIso
      (vertexFiberMap p _ f hf (nerveVertex c) ≫
        (weightedNerveFiberIso
          ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) c).inv ≫
        R.map (cocartesianStrictTransportEvaluate p c))
      (η.app (vertexFiber p (nerveVertex c)))) := by
  let T := cocartesianStrictTransportDiagram p
  let G := (T ⋙ R) ⋙ kanObjectForget
  have : ∀ i, KanComplex (G.obj i) := fun i => (R.obj (T.obj i)).isKanComplex
  have : Quasicategory (vertexFiber p (nerveVertex c)) :=
    vertexFiber_quasicategory_of_innerFibration p (nerveVertex c)
  have h := e.map (relativeFunctorFiberHom (simplicialReplacementProjection T)
    (weightedNerveProjection G) (nerveVertex c))
  rw [relativeFunctorFiberHom_vertex, relativeFunctorFiberHom_vertex] at h
  have h' := FunctorIso.postcomp (FunctorIso.precomp h (simplicialReplacementFiberMap T c))
    ((weightedNerveFiberIso G c).inv ≫ R.map (cocartesianStrictTransportEvaluate p c))
  have hleft : simplicialReplacementFiberMap T c ≫
      vertexFiberMap _ _ (cocartesianUniversalScaffold p ≫ f)
        (by rw [Category.assoc, hf, cocartesianUniversalScaffold_projection]) (nerveVertex c) =
      cocartesianStrictTransportEvaluate p c ≫ vertexFiberMap p _ f hf (nerveVertex c) := by
    apply vertexFiber_hom_ext
    simp only [Category.assoc, vertexFiberMap_ι]
    change simplicialReplacementConstantLift T c ≫ (cocartesianUniversalScaffold p ≫ f) = _
    rw [← Category.assoc, simplicialReplacementConstantLift_kanUniversalScaffold,
      Category.assoc]
  have hright := cocartesianKanWeightedScaffoldUnit_fiber p R η c
  change _ = η.app (T.obj c) ≫ weightedNerveFiberMap G c at hright
  simp only [← Category.assoc] at h'
  rw [hleft, hright] at h'
  simp only [Category.assoc] at h'
  have hn := η.naturality (cocartesianStrictTransportEvaluate p c)
  change cocartesianStrictTransportEvaluate p c ≫ η.app (vertexFiber p (nerveVertex c)) =
    η.app (T.obj c) ≫ R.map (cocartesianStrictTransportEvaluate p c) at hn
  simp only [weightedNerveFiberIso, asIso_inv, IsIso.hom_inv_id_assoc] at h'
  rw [← hn] at h'
  exact ⟨((cocartesianStrictTransportEvaluate_isQCatEquivalence p c).isPrecompositionEquivalence
    (R.obj (vertexFiber p (nerveVertex c))).obj).isFullyFaithful.preimageVertexIso h'⟩

/-- 元の全族からの同じ実射・厳密な底・全 fiber の Kan 単位回収をまとめて供給する。 -/
lemma exists_cocartesianKanWeightedUnit_fiber_recovery {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    ∃ f : E ⟶ weightedNerve ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget),
      ∃ hf : f ≫ weightedNerveProjection
        ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) = p,
      ∀ c : I, Nonempty (FunctorIso
        (vertexFiberMap p _ f hf (nerveVertex c) ≫
          (weightedNerveFiberIso
            ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) c).inv ≫
          R.map (cocartesianStrictTransportEvaluate p c))
        (η.app (vertexFiber p (nerveVertex c)))) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_cocartesianKanWeightedUnit p R η
  exact ⟨f, hf, fun c => cocartesianKanWeightedUnit_fiber_recovery p R η f hf e c⟩

end SerrePositivity.InfinityCategories
