module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrescribedCocartesianTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyPrism

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
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section

universe v
open HomotopicalAlgebra

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]


include fibD e SC SD in
/-- 元の cf 置換辺を全頂点で固定する coherent 左関手と、元の導来左関手への自然同型。 -/
lemma quillenCfLeftReplacement_transport_exists :
    ∃ (G : SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
        SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D))
      (H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = G ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) ∧
      (∀ x, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
          (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x)).edge) ∧
      (∀ x, G.app (Opposite.op ⦋0⦌) x =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x))) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD)) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageInfinity_quasicategory R adj SC SD
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cocartesianFibration R adj fibD e SC SD
  let i := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R
  let j := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R
  let p := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R
  let x (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)) _⦋0⦌) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)))
  let ee (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)) _⦋0⦌) :
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R).Edge (j.app (Opposite.op ⦋0⦌) y) (x y) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).src_eq.trans (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)) =
          (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R).app (Opposite.op ⦋0⦌) y
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object]
        rfl)
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).tgt_eq }
  obtain ⟨H, h0, hp, hc, hedge⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_cocartesianPrism_prescribed_vertices p j
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom_projection R) x ee
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge_projection R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge_isCocartesian R adj fibD e SC SD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H
  have hgp : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H) ≫ p = _
    rw [Category.assoc, hp]
    rfl
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) g hgp ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).inv
  have hGi : G ≫ i = g := by
    dsimp only [G, i]
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hGv (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)) _⦋0⦌) :
      G.app (Opposite.op ⦋0⦌) y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)) := by
    have hi : Mono i := by
      dsimp only [i]
      rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso_hom_ι]
      infer_instance
    apply (mono_iff_injective (i.app (Opposite.op ⦋0⦌))).mp
      ((NatTrans.mono_iff_mono_app i).mp hi _)
    have htgt := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism H h0 rfl) y).tgt_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge, hedge] at htgt
    have hv : g.app (Opposite.op ⦋0⦌) y = x y := htgt.symm.trans (ee y).tgt_eq
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R)).app (Opposite.op ⦋0⦌)
      (G.app (Opposite.op ⦋0⦌) y) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
    exact (congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) y) hGi).trans hv
  refine ⟨G, H, h0, hGi.symm, hp, hc, hedge, hGv, ?_⟩
  let b := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv
  let t := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom
  let Gf := b ≫ G ≫ t
  let K := ((Δ[1] : SSet.{max u v}) ◁ b) ≫ H
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge Gf := by
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · dsimp only [K]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h0]
      dsimp only [j]
      rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
      simp only [b, Iso.inv_hom_id_assoc]
      rfl
    · have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = G ≫ i := hGi.symm
      dsimp only [K]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, ht]
      change b ≫ G ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R =
        (b ≫ G ≫ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).hom) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
      simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso_hom_ι]
    · dsimp only [K]
      rw [Category.assoc, hp]
      have he : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge =
          (𝟙 (Δ[1] : SSet.{max u v})) := by
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply SSet.stdSimplex.ext
        intro k
        fin_cases k <;> rfl
      rw [he, Category.comp_id]
      rfl
    · intro v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), b.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1)))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
      exact hc (b.app _ v)
  obtain ⟨hiso⟩ := hT.functorIso p _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p _)
  have h := (hiso.precomp (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom).postcomp
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).inv
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).hom ≫ Gf) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfTopFiberIso R).inv)
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived R adj fibD e SC SD) at h
  simpa only [Gf, b, t, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using (Nonempty.intro h)

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
