module

public import SerrePositivity.InfinityCategories.HomotopyLimits.OrdinaryCoherentNatTransPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfReplacementNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfRightReplacement

/-!
概要：元の通常の右 cf 置換関手の nerve と、元の導来右関手を自然同型で比較する。
方針：元の通常の比較の prism と、同じ終点の Cartesian 輸送の一意性を使う。
規約：全対象・全射の作用を指定された関手のまま比較する。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
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
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))



include SC SD cofC in
/-- 元の通常の右置換関手の比較自然変換を、全指定辺を保持する Cartesian prism へ写す。 -/
lemma quillenCfRightOrdinaryPrism_exists :
    ∃ H : (Δ[1] : SSet.{max u v}) ⊗ nerve (CofibrantFibrantObjects D) ⟶
      QuillenCfCollageInfinity R,
      prismEndpoint 0 _ ≫ H =
        (nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
          nerveToCoherent (CofibrantFibrantObjects C)) ≫ quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H =
        nerveToCoherent (CofibrantFibrantObjects D) ≫ quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R =
        CategoryTheory.CartesianMonoidalCategory.fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ y, IsCartesianEdge (quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant y 1))) ∧
      (∀ Y : CofibrantFibrantObjects D, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
          PinchedHom.constant (nerveVertex Y) 1) =
            (quillenCfRightLiftEdge R adj cofC Y).edge) := by
  let η := quillenCfRightReplacementComparison R adj cofC
  let H := ordinaryCoherentNatTransPrism η
  have h0 : prismEndpoint 0 _ ≫ H =
      (nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
        nerveToCoherent (CofibrantFibrantObjects C)) ≫ quillenCfCollageBottomNerve R := by
    have hz := ordinaryCoherentNatTransPrism_zero η
    refine hz.trans ?_
    change nerveMap (quillenCfRightReplacementFunctor R adj cofC ⋙
      coherentEnrichedUnderlyingFunctor (quillenCfCollageBottom R)) ≫
        nerveToCoherent (QuillenCfCollage R) = _
    calc
      _ = (nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
          nerveMap (coherentEnrichedUnderlyingFunctor (quillenCfCollageBottom R))) ≫
            nerveToCoherent (QuillenCfCollage R) := by rfl
      _ = _ := by
        rw [Category.assoc, nerveToCoherent_enriched_naturality]
        rfl
  have h1 : prismEndpoint 1 _ ≫ H =
      nerveToCoherent (CofibrantFibrantObjects D) ≫ quillenCfCollageTopNerve R :=
    (ordinaryCoherentNatTransPrism_one η).trans
      (nerveToCoherent_enriched_naturality (quillenCfCollageTop R))
  have hp : H ≫ quillenCfCollageProjection R =
      CategoryTheory.CartesianMonoidalCategory.fst (Δ[1] : SSet.{max u v}) _ := by
    apply prism_projection_of_endpoints
    · rw [h0]
      simp only [Category.assoc, quillenCfCollageBottom_projection, SSet.comp_const]
    · rw [h1]
      simp only [Category.assoc, quillenCfCollageTop_projection, SSet.comp_const]
  refine ⟨H, h0, h1, hp, ?_, ?_⟩
  · intro y
    have hy : nerveVertex (y.obj 0) = y := ComposableArrows.ext₀ rfl
    rw [← hy]
    change IsCartesianEdge (quillenCfCollageProjection R)
      ((ordinaryCoherentNatTransPrism η).app (Opposite.op ⦋1⦌) _)
    rw [ordinaryCoherentNatTransPrism_vertexEdge]
    exact quillenCfRightLiftEdge_isCartesian R adj cofC SC SD (y.obj 0)
  · intro Y
    change (ordinaryCoherentNatTransPrism η).app (Opposite.op ⦋1⦌) _ = _
    rw [ordinaryCoherentNatTransPrism_vertexEdge]
    rfl

include SC SD cofC in
/-- 元の通常の右置換関手の nerve と、元の導来右関手の通常の nerve 上の制限は自然同型。 -/
lemma quillenCfRightDerived_ordinaryComparison :
    Nonempty (FunctorIso
      (nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
        nerveToCoherent (CofibrantFibrantObjects C))
      (nerveToCoherent (CofibrantFibrantObjects D) ≫
        quillenCfRightDerived R adj SC SD cofC)) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  let p := quillenCfCollageProjection R
  let i := quillenCfCollageBottomNerve R
  let T := nerveToCoherent (CofibrantFibrantObjects D)
  let P := nerveMap (quillenCfRightReplacementFunctor R adj cofC) ≫
    nerveToCoherent (CofibrantFibrantObjects C)
  let G := T ≫ quillenCfRightDerived R adj SC SD cofC
  obtain ⟨H, hH0, hH1, hHp, hHc, _⟩ :=
    quillenCfRightOrdinaryPrism_exists R adj SC SD cofC
  obtain ⟨K, hK0, hK1, hKp, hKc⟩ := quillenCfRightDerived_transport R adj SC SD cofC
  let K' := ((Δ[1] : SSet.{max u v}) ◁ T) ≫ K
  have hk0 : prismEndpoint 0 _ ≫ K' = G ≫ i := by
    dsimp only [K']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK0]
    rfl
  have hk1 : prismEndpoint 1 _ ≫ K' = prismEndpoint 1 _ ≫ H := by
    dsimp only [K']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK1, hH1]
  have hkp : K' ≫ p = CategoryTheory.CartesianMonoidalCategory.fst
      (Δ[1] : SSet.{max u v}) _ := by
    dsimp only [K', p]
    rw [Category.assoc, hKp]
    rfl
  have hkc : ∀ y, IsCartesianEdge p (K'.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant y 1)) := by
    intro y
    change IsCartesianEdge p (K.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), T.app _ (PinchedHom.constant y 1)))
    rw [pinchedConstant_map]
    exact hKc (T.app _ y)
  obtain ⟨α, hα0, hα1, hαp, hαinv⟩ := cartesianPrism_sourceComparison p H K' hHp hkp
    hk1 hHc hkc
  let η := vertexFiberLift p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) α hαp ≫
    (quillenCfBottomFiberIso R).inv
  have hηi : η ≫ i = α := by
    dsimp only [η, i]
    rw [← quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberLift_ι _ _ _ _
  have hi : Mono i := by
    dsimp only [i]
    rw [← quillenCfBottomFiberIso_hom_ι]
    infer_instance
  have hη0 : prismEndpoint 0 _ ≫ η = P := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hηi, hα0, hH0]
  have hη1 : prismEndpoint 1 _ ≫ η = G := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hηi, hα1, hk0]
  let Q := homotopyOfPrism η hη0 hη1
  refine ⟨functorIsoOfPointwiseInvertibleHomotopy Q ?_⟩
  intro y
  apply (quillenCfCollageBottomNerve_isFullyFaithful R adj SC SD).reflects_isInvertibleEdge
  have hed : ((simplicialHomotopyVertexEdge Q y).toTruncated.map
      ((truncation 2).map i)).edge =
      (simplicialHomotopyVertexEdge (homotopyOfPrism α hα0 hα1) y).edge := by
    change i.app (Opposite.op ⦋1⦌) (simplicialHomotopyVertexEdge Q y).edge = _
    rw [homotopyOfPrism_vertexEdge, homotopyOfPrism_vertexEdge]
    exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant y 1)) hηi
  exact (isInvertibleEdge_congr hed).2 (hαinv y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
