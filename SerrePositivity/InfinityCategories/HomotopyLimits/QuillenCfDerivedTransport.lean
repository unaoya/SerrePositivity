module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianEdgeTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfBifibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfEndpointEquivalence

/-!
概要：元の cf nerve 間の左右の導来関手と、元の対応圏内の輸送 prism を構成する。
方針：区間の輸送を両端 fiber の同型で挟み、全空間への元の包含との一致を使う。
規約：単位・余単位と随伴性は別途証明する。使われ方：HTT 5.2.4.6 の導来 ∞ 随伴。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]

/-- 元の cf 圏の coherent nerve 間の左導来関手。 -/
def quillenCfLeftDerived : SimplicialNerve (CofibrantFibrantObjects C) ⟶
    SimplicialNerve (CofibrantFibrantObjects D) := by
  have := quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  exact (quillenCfBottomFiberIso R).hom ≫
    edgeTransport (quillenCfCollageProjection R) homotopyIntervalEdge ≫
      (quillenCfTopFiberIso R).inv

include fibD e SC SD in
/-- 左導来関手は、元の両包含を両端とする coCartesian な輸送 prism を持つ。 -/
lemma quillenCfLeftDerived_transport :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects C) ⟶
        QuillenCfCollageInfinity R,
      prismEndpoint 0 _ ≫ H = quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H =
        quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      ∀ v : (SimplicialNerve (CofibrantFibrantObjects C)) _⦋0⦌,
        IsCocartesianEdge (quillenCfCollageProjection R)
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant v 1)) := by
  have := quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  obtain ⟨H, h0, h1, hb, hc⟩ := edgeTransport_isTransport
    (quillenCfCollageProjection R) homotopyIntervalEdge
  refine ⟨((Δ[1] : SSet.{max u v}) ◁ (quillenCfBottomFiberIso R).hom) ≫ H,
    ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h0,
      quillenCfBottomFiberIso_hom_ι]
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h1]
    change (quillenCfBottomFiberIso R).hom ≫ _ =
      ((quillenCfBottomFiberIso R).hom ≫ _ ≫ (quillenCfTopFiberIso R).inv) ≫ _
    rw [← quillenCfTopFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, hb]
    have he : SSet.yonedaEquiv.symm homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{max u v})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [he, Category.comp_id]
    rfl
  · intro v
    change IsCocartesianEdge (quillenCfCollageProjection R)
      (H.app (Opposite.op ⦋1⦌) (_, (quillenCfBottomFiberIso R).hom.app _
        (PinchedHom.constant v 1)))
    rw [pinchedConstant_map]
    exact hc ((quillenCfBottomFiberIso R).hom.app _ v)

variable (cofC : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

/-- 元の cf 圏の coherent nerve 間の右導来関手。 -/
def quillenCfRightDerived : SimplicialNerve (CofibrantFibrantObjects D) ⟶
    SimplicialNerve (CofibrantFibrantObjects C) := by
  have := quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  exact (quillenCfTopFiberIso R).hom ≫
    cartesianEdgeTransport (quillenCfCollageProjection R) homotopyIntervalEdge ≫
      (quillenCfBottomFiberIso R).inv

include adj SC SD cofC in
/-- 右導来関手は、元の両包含を両端とする Cartesian な輸送 prism を持つ。 -/
lemma quillenCfRightDerived_transport :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects D) ⟶
        QuillenCfCollageInfinity R,
      prismEndpoint 0 _ ≫ H =
        quillenCfRightDerived R adj SC SD cofC ≫ quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H = quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      ∀ v : (SimplicialNerve (CofibrantFibrantObjects D)) _⦋0⦌,
        IsCartesianEdge (quillenCfCollageProjection R)
          (H.app (Opposite.op ⦋1⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant v 1)) := by
  have := quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  obtain ⟨H, h0, h1, hb, hc⟩ := cartesianEdgeTransport_witness
    (quillenCfCollageProjection R) homotopyIntervalEdge
  refine ⟨((Δ[1] : SSet.{max u v}) ◁ (quillenCfTopFiberIso R).hom) ≫ H,
    ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h0]
    change (quillenCfTopFiberIso R).hom ≫ _ =
      ((quillenCfTopFiberIso R).hom ≫ _ ≫ (quillenCfBottomFiberIso R).inv) ≫ _
    rw [← quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h1,
      quillenCfTopFiberIso_hom_ι]
  · rw [Category.assoc, hb]
    have he : SSet.yonedaEquiv.symm homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{max u v})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [he, Category.comp_id]
    rfl
  · intro v
    change IsCartesianEdge (quillenCfCollageProjection R)
      (H.app (Opposite.op ⦋1⦌) (_, (quillenCfTopFiberIso R).hom.app _
        (PinchedHom.constant v 1)))
    rw [pinchedConstant_map]
    exact hc ((quillenCfTopFiberIso R).hom.app _ v)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
