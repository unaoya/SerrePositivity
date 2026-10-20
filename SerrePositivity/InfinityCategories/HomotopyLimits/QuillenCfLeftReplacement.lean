module

public import SerrePositivity.InfinityCategories.HomotopyLimits.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrescribedCocartesianTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyPrism

/-!
概要：元の LX→R_D(LX) の随伴像を全頂点で保持する coherent 左関手を、元の導来左関手と比較する。
方針：全頂点の相対延長と cocartesian transport の選択の一意性を使う。
規約：元の指定された置換辺を変更しない。使われ方：HTT 5.2.4.6 の cf 比較。
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
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]


include fibD e SC SD in
/-- 元の cf 置換辺を全頂点で固定する coherent 左関手と、元の導来左関手への自然同型。 -/
lemma quillenCfLeftReplacement_transport_exists :
    ∃ (G : SimplicialNerve (CofibrantFibrantObjects C) ⟶
        SimplicialNerve (CofibrantFibrantObjects D))
      (H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (CofibrantFibrantObjects C) ⟶
        QuillenCfCollageInfinity R),
      prismEndpoint 0 _ ≫ H = quillenCfCollageBottomNerve R ∧
      prismEndpoint 1 _ ≫ H = G ≫ quillenCfCollageTopNerve R ∧
      H ≫ quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, IsCocartesianEdge (quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1))) ∧
      (∀ x, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), PinchedHom.constant x 1) =
          (quillenCfLeftLiftEdge R adj fibD (coherentNerveObject x)).edge) ∧
      (∀ x, G.app (Opposite.op ⦋0⦌) x =
        coherentNerveVertex (quillenCfLeftLiftObject R adj fibD (coherentNerveObject x))) ∧
      Nonempty (FunctorIso G (quillenCfLeftDerived R adj fibD e SC SD)) := by
  have := cofibrantFibrantObjects_nerve_quasicategory SC
  have := cofibrantFibrantObjects_nerve_quasicategory SD
  have := quillenCfCollageInfinity_quasicategory R adj SC SD
  have := quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  let i := quillenCfCollageTopNerve R
  let j := quillenCfCollageBottomNerve R
  let p := quillenCfCollageProjection R
  let x (y : (SimplicialNerve (CofibrantFibrantObjects C)) _⦋0⦌) :=
    coherentNerveVertex ((quillenCfCollageTop R).obj
      (quillenCfLeftLiftObject R adj fibD (coherentNerveObject y)))
  let ee (y : (SimplicialNerve (CofibrantFibrantObjects C)) _⦋0⦌) :
      (QuillenCfCollageInfinity R).Edge (j.app (Opposite.op ⦋0⦌) y) (x y) :=
    { edge := (quillenCfLeftLiftEdge R adj fibD (coherentNerveObject y)).edge
      src_eq := (quillenCfLeftLiftEdge R adj fibD (coherentNerveObject y)).src_eq.trans (by
        change coherentNerveVertex ((quillenCfCollageBottom R).obj (coherentNerveObject y)) =
          (quillenCfCollageBottomNerve R).app (Opposite.op ⦋0⦌) y
        rw [← coherentNerveMap_vertex, coherentNerveVertex_object]
        rfl)
      tgt_eq := (quillenCfLeftLiftEdge R adj fibD (coherentNerveObject y)).tgt_eq }
  obtain ⟨H, h0, hp, hc, hedge⟩ := exists_cocartesianPrism_prescribed_vertices p j
    (quillenCfCollageBottom_projection R) x ee
    (fun y ↦ quillenCfLeftLiftEdge_projection R adj fibD (coherentNerveObject y))
    (fun y ↦ quillenCfLeftLiftEdge_isCocartesian R adj fibD e SC SD (coherentNerveObject y))
  let g := prismEndpoint 1 _ ≫ H
  have hgp : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    change (prismEndpoint 1 _ ≫ H) ≫ p = _
    rw [Category.assoc, hp]
    rfl
  let G := vertexFiberLift p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) g hgp ≫
    (quillenCfTopFiberIso R).inv
  have hGi : G ≫ i = g := by
    dsimp only [G, i]
    rw [← quillenCfTopFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberLift_ι _ _ _ _
  have hGv (y : (SimplicialNerve (CofibrantFibrantObjects C)) _⦋0⦌) :
      G.app (Opposite.op ⦋0⦌) y =
        coherentNerveVertex (quillenCfLeftLiftObject R adj fibD (coherentNerveObject y)) := by
    have hi : Mono i := by
      dsimp only [i]
      rw [← quillenCfTopFiberIso_hom_ι]
      infer_instance
    apply (mono_iff_injective (i.app (Opposite.op ⦋0⦌))).mp
      ((NatTrans.mono_iff_mono_app i).mp hi _)
    have htgt := (simplicialHomotopyVertexEdge (homotopyOfPrism H h0 rfl) y).tgt_eq
    rw [homotopyOfPrism_vertexEdge, hedge] at htgt
    have hv : g.app (Opposite.op ⦋0⦌) y = x y := htgt.symm.trans (ee y).tgt_eq
    change (coherentNerveMap (quillenCfCollageTop R)).app (Opposite.op ⦋0⦌)
      (G.app (Opposite.op ⦋0⦌) y) =
        (coherentNerveMap (quillenCfCollageTop R)).app (Opposite.op ⦋0⦌)
          (coherentNerveVertex (quillenCfLeftLiftObject R adj fibD (coherentNerveObject y)))
    rw [coherentNerveMap_vertex]
    exact (congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) y) hGi).trans hv
  refine ⟨G, H, h0, hGi.symm, hp, hc, hedge, hGv, ?_⟩
  let b := (quillenCfBottomFiberIso R).inv
  let t := (quillenCfTopFiberIso R).hom
  let Gf := b ≫ G ≫ t
  let K := ((Δ[1] : SSet.{max u v}) ◁ b) ≫ H
  have hT : IsEdgeTransport p homotopyIntervalEdge Gf := by
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · dsimp only [K]
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, h0]
      dsimp only [j]
      rw [← quillenCfBottomFiberIso_hom_ι]
      simp only [b, Iso.inv_hom_id_assoc]
      rfl
    · have ht : prismEndpoint 1 _ ≫ H = G ≫ i := hGi.symm
      dsimp only [K]
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, ht]
      change b ≫ G ≫ quillenCfCollageTopNerve R =
        (b ≫ G ≫ (quillenCfTopFiberIso R).hom) ≫
          vertexFiberι (quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
      simp only [Category.assoc, quillenCfTopFiberIso_hom_ι]
    · dsimp only [K]
      rw [Category.assoc, hp]
      have he : SSet.yonedaEquiv.symm homotopyIntervalEdge.edge =
          (𝟙 (Δ[1] : SSet.{max u v})) := by
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply SSet.stdSimplex.ext
        intro k
        fin_cases k <;> rfl
      rw [he, Category.comp_id]
      rfl
    · intro v
      change IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), b.app _ (PinchedHom.constant v 1)))
      rw [pinchedConstant_map]
      exact hc (b.app _ v)
  obtain ⟨hiso⟩ := hT.functorIso p homotopyIntervalEdge (edgeTransport_isTransport p _)
  have h := (hiso.precomp (quillenCfBottomFiberIso R).hom).postcomp
    (quillenCfTopFiberIso R).inv
  change FunctorIso
    (((quillenCfBottomFiberIso R).hom ≫ Gf) ≫ (quillenCfTopFiberIso R).inv)
    (quillenCfLeftDerived R adj fibD e SC SD) at h
  simpa only [Gf, b, t, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using (Nonempty.intro h)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
