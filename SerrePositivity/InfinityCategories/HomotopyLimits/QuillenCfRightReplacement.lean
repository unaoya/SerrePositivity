module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfFullyFaithful
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrescribedCartesianTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianSourceComparison

/-!
概要：元の Q(RY)→RY を全頂点で保持する coherent な右関手を、元の導来右関手と比較する。
方針：全頂点で固定した相対延長と Cartesian 辺の消去則を使用する。
規約：指定した元の置換の比較射を変更しない。使われ方：HTT 5.2.4.6 の cf 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

universe v
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
/-- 元の cf 置換辺を全頂点で固定する coherent な右関手と、元の導来右関手への自然同型。 -/
lemma quillenCfRightReplacement_transport_exists :
    ∃ (G : SimplicialNerve (CofibrantFibrantObjects D) ⟶
        SimplicialNerve (CofibrantFibrantObjects C))
      (H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects D) ⟶
        QuillenCfCollageInfinity R),
      prismEndpoint 0 _ ≫ H = G ≫ quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H = quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ y, IsCartesianEdge (quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant y 1))) ∧
      (∀ y, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant y 1) =
          (quillenCfRightLiftEdge R adj cofC (coherentNerveObject y)).edge) ∧
      (∀ y, G.app (Opposite.op ⦋0⦌) y =
        coherentNerveVertex (quillenCfRightLiftObject R adj cofC (coherentNerveObject y))) ∧
      Nonempty (FunctorIso G (quillenCfRightDerived R adj SC SD cofC)) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  let i := quillenCfCollageBottomNerve R
  let j := quillenCfCollageTopNerve R
  let p := quillenCfCollageProjection R
  let x (y : (SimplicialNerve (CofibrantFibrantObjects D)) _⦋0⦌) :=
    coherentNerveVertex ((quillenCfCollageBottom R).obj
      (quillenCfRightLiftObject R adj cofC (coherentNerveObject y)))
  let ee (y : (SimplicialNerve (CofibrantFibrantObjects D)) _⦋0⦌) :
      (QuillenCfCollageInfinity R).Edge (x y) (j.app (Opposite.op ⦋0⦌) y) :=
    { edge := (quillenCfRightLiftEdge R adj cofC (coherentNerveObject y)).edge
      src_eq := (quillenCfRightLiftEdge R adj cofC (coherentNerveObject y)).src_eq
      tgt_eq := (quillenCfRightLiftEdge R adj cofC (coherentNerveObject y)).tgt_eq.trans (by
        change coherentNerveVertex ((quillenCfCollageTop R).obj (coherentNerveObject y)) =
          (quillenCfCollageTopNerve R).app (Opposite.op ⦋0⦌) y
        rw [← coherentNerveMap_vertex, coherentNerveVertex_object]
        rfl) }
  obtain ⟨H, h1, hp, hc, hedge⟩ := exists_cartesianPrism_prescribed_vertices p j
    (quillenCfCollageTop_projection R) x ee
    (fun y ↦ quillenCfRightLiftEdge_projection R adj cofC (coherentNerveObject y))
    (fun y ↦ quillenCfRightLiftEdge_isCartesian R adj cofC SC SD (coherentNerveObject y))
  let g := prismEndpoint 0 _ ≫ H
  have hgp : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change (prismEndpoint 0 _ ≫ H) ≫ p = _
    rw [Category.assoc, hp]
    rfl
  let G := vertexFiberLift p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) g hgp ≫
    (quillenCfBottomFiberIso R).inv
  have hGi : G ≫ i = g := by
    dsimp only [G, i]
    rw [← quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberLift_ι _ _ _ _
  have hGv (y : (SimplicialNerve (CofibrantFibrantObjects D)) _⦋0⦌) :
      G.app (Opposite.op ⦋0⦌) y =
        coherentNerveVertex (quillenCfRightLiftObject R adj cofC (coherentNerveObject y)) := by
    have hi : Mono i := by
      dsimp only [i]
      rw [← quillenCfBottomFiberIso_hom_ι]
      infer_instance
    apply (mono_iff_injective (i.app (Opposite.op ⦋0⦌))).mp
      ((NatTrans.mono_iff_mono_app i).mp hi _)
    have hsrc := (simplicialHomotopyVertexEdge (homotopyOfPrism H rfl h1) y).src_eq
    rw [homotopyOfPrism_vertexEdge, hedge] at hsrc
    have hv : g.app (Opposite.op ⦋0⦌) y = x y :=
      hsrc.symm.trans (ee y).src_eq
    change (coherentNerveMap (quillenCfCollageBottom R)).app (Opposite.op ⦋0⦌)
      (G.app (Opposite.op ⦋0⦌) y) =
        (coherentNerveMap (quillenCfCollageBottom R)).app (Opposite.op ⦋0⦌)
          (coherentNerveVertex (quillenCfRightLiftObject R adj cofC (coherentNerveObject y)))
    rw [coherentNerveMap_vertex]
    exact (congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) y) hGi).trans hv
  obtain ⟨K, hk0, hk1, hkp, hkc⟩ := quillenCfRightDerived_transport R adj SC SD cofC
  obtain ⟨α, hα0, hα1, hαp, hαinv⟩ := cartesianPrism_sourceComparison p H K hp hkp
    (hk1.trans h1.symm) hc hkc
  refine ⟨G, H, hGi.symm, h1, hp, hc, hedge, hGv, ?_⟩
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
  have hη0 : prismEndpoint 0 _ ≫ η = G := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hηi, hα0]
    exact hGi.symm
  have hη1 : prismEndpoint 1 _ ≫ η = quillenCfRightDerived R adj SC SD cofC := by
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
