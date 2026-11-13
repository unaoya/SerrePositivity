module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfDerivedTransport
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrescribedCartesianTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CartesianSourceComparison

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
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section

universe v
open HomotopicalAlgebra

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))



include SC SD cofC in
/-- 元の cf 置換辺を全頂点で固定する coherent な右関手と、元の導来右関手への自然同型。 -/
lemma quillenCfRightReplacement_transport_exists :
    ∃ (G : SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ⟶
        SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C))
      (H : (Δ[1] : SSet.{max u v}) ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) ⟶
        _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = G ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = fst (Δ[1] : SSet.{max u v}) _ ∧
      (∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R)
        (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1))) ∧
      (∀ y, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1) =
          (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).edge) ∧
      (∀ y, G.app (Opposite.op ⦋0⦌) y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))) ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC)) := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SC
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.cofibrantFibrantObjects_nerve_quasicategory SD
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageInfinity_quasicategory R adj SC SD
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration R adj SC SD cofC
  let i := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve R
  let j := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R
  let p := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R
  let x (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)) _⦋0⦌) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R).obj
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)))
  let ee (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)) _⦋0⦌) :
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R).Edge (x y) (j.app (Opposite.op ⦋0⦌) y) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).src_eq
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)).tgt_eq.trans (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)) =
          (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTopNerve R).app (Opposite.op ⦋0⦌) y
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object]
        rfl) }
  obtain ⟨H, h1, hp, hc, hedge⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.exists_cartesianPrism_prescribed_vertices p j
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop_projection R) x ee
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge_projection R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))
    (fun y ↦ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge_isCartesian R adj cofC SC SD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y))
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H
  have hgp : g ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H) ≫ p = _
    rw [Category.assoc, hp]
    rfl
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) g hgp ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv
  have hGi : G ≫ i = g := by
    dsimp only [G, i]
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hGv (y : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)) _⦋0⦌) :
      G.app (Opposite.op ⦋0⦌) y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)) := by
    have hi : Mono i := by
      dsimp only [i]
      rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
      infer_instance
    apply (mono_iff_injective (i.app (Opposite.op ⦋0⦌))).mp
      ((NatTrans.mono_iff_mono_app i).mp hi _)
    have hsrc := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism H rfl h1) y).src_eq
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge, hedge] at hsrc
    have hv : g.app (Opposite.op ⦋0⦌) y = x y :=
      hsrc.symm.trans (ee y).src_eq
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R)).app (Opposite.op ⦋0⦌)
      (G.app (Opposite.op ⦋0⦌) y) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
    exact (congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) y) hGi).trans hv
  obtain ⟨K, hk0, hk1, hkp, hkc⟩ := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived_transport R adj SC SD cofC
  obtain ⟨α, hα0, hα1, hαp, hαinv⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianPrism_sourceComparison p H K hp hkp
    (hk1.trans h1.symm) hc hkc
  refine ⟨G, H, hGi.symm, h1, hp, hc, hedge, hGv, ?_⟩
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) α hαp ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso R).inv
  have hηi : η ≫ i = α := by
    dsimp only [η, i]
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hi : Mono i := by
    dsimp only [i]
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfBottomFiberIso_hom_ι]
    infer_instance
  have hη0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ η = G := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hηi, hα0]
    exact hGi.symm
  have hη1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ η = _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightDerived R adj SC SD cofC := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hηi, hα1, hk0]
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism η hη0 hη1
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy Q ?_⟩
  intro y
  apply (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottomNerve_isFullyFaithful R adj SC SD).reflects_isInvertibleEdge
  have hed : ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Q y).toTruncated.map
      ((truncation 2).map i)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism α hα0 hα1) y).edge := by
    change i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge Q y).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism_vertexEdge]
    exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1)) hηi
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hed).2 (hαinv y)

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
