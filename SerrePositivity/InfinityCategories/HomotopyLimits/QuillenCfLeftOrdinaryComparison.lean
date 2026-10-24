module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CocartesianPrismComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.EndpointFunctorIsoReflection
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfFullyFaithful
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfLeftReplacement
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfReplacementNaturality

/-!
概要：元の通常の左 cf 置換関手の nerve と元の導来左関手を比較する。
方針：元の比較自然変換の prism と coCartesian 輸送の一意性を使う。
規約：全対象・全射を指定関手のまま比較。使われ方：HTT 5.2.4.6 の集約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

open HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Coherent
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

include fibD e SC SD in
/-- 元の通常の左置換比較を、元の全候補辺を保持する coCartesian prism へ写す。 -/
lemma quillenCfLeftOrdinaryPrism_exists :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ nerve (CofibrantFibrantObjects C) ⟶
      QuillenCfCollageInfinity R,
      prismEndpoint 0 _ ≫ H =
        nerveToCoherent (CofibrantFibrantObjects C) ≫ quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H =
        (nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
          nerveToCoherent (CofibrantFibrantObjects D)) ≫ quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, IsCocartesianEdge (quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1))) ∧
      (∀ X : CofibrantFibrantObjects C, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
          PinchedHom.constant (nerveVertex X) 1) =
            (quillenCfLeftLiftEdge R adj fibD X).edge) := by
  let η := quillenCfLeftReplacementComparison R adj fibD
  let H := ordinaryCoherentNatTransPrism η
  have h0 : prismEndpoint 0 _ ≫ H =
      nerveToCoherent (CofibrantFibrantObjects C) ≫ quillenCfCollageBottomNerve R :=
    (ordinaryCoherentNatTransPrism_zero η).trans
      (nerveToCoherent_enriched_naturality (quillenCfCollageBottom R))
  have h1 : prismEndpoint 1 _ ≫ H =
      (nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
        nerveToCoherent (CofibrantFibrantObjects D)) ≫ quillenCfCollageTopNerve R := by
    have hz := ordinaryCoherentNatTransPrism_one η
    refine hz.trans ?_
    change nerveMap (quillenCfLeftReplacementFunctor R adj fibD ⋙
      coherentEnrichedUnderlyingFunctor (quillenCfCollageTop R)) ≫
        nerveToCoherent (QuillenCfCollage R) = _
    calc
      _ = (nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
          nerveMap (coherentEnrichedUnderlyingFunctor (quillenCfCollageTop R))) ≫
            nerveToCoherent (QuillenCfCollage R) := by rfl
      _ = _ := by
        rw [Category.assoc, nerveToCoherent_enriched_naturality]
        rfl
  have hp : H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ := by
    apply prism_projection_of_endpoints
    · rw [h0]
      simp only [Category.assoc, quillenCfCollageBottom_projection, SSet.comp_const]
    · rw [h1]
      simp only [Category.assoc, quillenCfCollageTop_projection, SSet.comp_const]
  refine ⟨H, h0, h1, hp, ?_, ?_⟩
  · intro x
    have hx : nerveVertex (x.obj 0) = x := ComposableArrows.ext₀ rfl
    rw [← hx]
    change IsCocartesianEdge (quillenCfCollageProjection R)
      ((ordinaryCoherentNatTransPrism η).app (Opposite.op ⦋1⦌) _)
    rw [ordinaryCoherentNatTransPrism_vertexEdge]
    exact quillenCfLeftLiftEdge_isCocartesian R adj fibD e SC SD (x.obj 0)
  · intro X
    change (ordinaryCoherentNatTransPrism η).app (Opposite.op ⦋1⦌) _ = _
    rw [ordinaryCoherentNatTransPrism_vertexEdge]
    rfl

include fibD e SC SD in
/-- 元の通常の左 cf 置換関手の nerve と、元の導来左関手との自然同型。 -/
lemma quillenCfLeftDerived_ordinaryComparison :
    Nonempty (FunctorIso
      (nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
        nerveToCoherent (CofibrantFibrantObjects D))
      (nerveToCoherent (CofibrantFibrantObjects C) ≫
        quillenCfLeftDerived R adj fibD e SC SD)) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  let p := quillenCfCollageProjection R
  let j := quillenCfCollageTopNerve R
  let T := nerveToCoherent (CofibrantFibrantObjects C)
  let P := nerveMap (quillenCfLeftReplacementFunctor R adj fibD) ≫
    nerveToCoherent (CofibrantFibrantObjects D)
  let G := T ≫ quillenCfLeftDerived R adj fibD e SC SD
  obtain ⟨H, hH0, hH1, hHp, hHc, _⟩ := quillenCfLeftOrdinaryPrism_exists R adj fibD e SC SD
  obtain ⟨K, hK0, hK1, hKp, hKc⟩ := quillenCfLeftDerived_transport R adj fibD e SC SD
  let K' := ((Δ[1] : SSet.{max u v}) ◁ T) ≫ K
  have hk0 : prismEndpoint 0 _ ≫ K' = prismEndpoint 0 _ ≫ H := by
    dsimp only [K']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK0, hH0]
  have hk1 : prismEndpoint 1 _ ≫ K' = G ≫ j := by
    dsimp only [K']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK1]
    rfl
  have hkp : K' ≫ p = fst (Δ[1] : SSet.{max u v}) _ := by
    dsimp only [K', p]
    rw [Category.assoc, hKp]
    rfl
  have hkc : ∀ x, IsCocartesianEdge p (K'.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1)) := by
    intro x
    change IsCocartesianEdge p (K.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), T.app _ (PinchedHom.constant x 1)))
    rw [pinchedConstant_map]
    exact hKc (T.app _ x)
  obtain ⟨hiso⟩ := cocartesianPrism_targetFunctorIso p H K' hk0.symm (hHp.trans hkp.symm)
    hHc hkc
  let eiso : FunctorIso (P ≫ j) (G ≫ j) := SerrePositivity.InfinityCategories.functorIsoTransport hiso hH1 hk1
  exact endpointFunctorIso_reflection p 1 j (quillenCfCollageTopNerve_isFullyFaithful R adj SC SD)
    (quillenCfTopFiberIso R) (quillenCfTopFiberIso_hom_ι R) eiso

end
end SerrePositivity.InfinityCategories.HomotopyLimits
