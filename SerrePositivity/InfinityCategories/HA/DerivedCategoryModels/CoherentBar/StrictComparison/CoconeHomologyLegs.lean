module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoconeVertexRecovery
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentVertexInclusion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ClosedEdgeRecovery
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentCoconeHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopyComponent
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegEdge

/-!
概要：指定 native 余錐のホモロジー脚は、同じ零次元係数の実閉射のホモロジー。
方針：指定垂直辺の成分公式と端点移送を照合する。
規約：元の余錐の脚を任意の同型へ置き換えない。
使われ方：native 増大の C1 余核比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgBarCoconeVertexModuleMap_edge (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (s : I _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeVertexModuleMap R D G c s =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_vertex R D G s)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c) (ULift.up s)).toTruncated := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeVertexModuleMap_eq]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)
      (ULift.up s)).edge = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D G c s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeHomotopyLeg_edge c (ULift.up s)
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarEdgeClosed_recover_transport R D
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c) (ULift.up s)).toTruncated he
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_source R D G c s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_last R D G c s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_vertex R D G s) rfl
  simpa only [eqToHom_refl, Category.comp_id] using! h

variable {J : Type u} [PartialOrder J]
  (H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentCoconeHomology_leg (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone H) (x : D) (q : ℤ) (j : J) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology R D H c x q).ι.app j =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D H x q j).hom ≫
        HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)
              (ULift.up (nerveEquiv.symm j))).toTruncated)) q := by
  change (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyHomology R D x q).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R (RightModule R D)).map
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarHomotopyNatTrans₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)).app
          ⟨ULift.up (nerveEquiv.symm j)⟩)) ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarHomotopyNatTrans₂_app, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0_homMk]
  exact (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).hom.naturality
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c)
          (ULift.up (nerveEquiv.symm j))).toTruncated))

lemma dgCoherentCoconeHomology_source_leg (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone H) (x : D) (q : ℤ)
    (s : (nerve J) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D H x q 0 s).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentCoconeHomology R D H c x q).ι.app (s.obj 0) =
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeVertexModuleMap R D H c s)) q := by
  obtain ⟨j, rfl⟩ := (nerveEquiv (C := J)).symm.surjective s
  rw [dgCoherentCoconeHomology_leg, dgBarCoconeVertexModuleMap_edge,
    Functor.map_comp, HomologicalComplex.homologyMap_comp]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso,
    Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    Functor.mapIso_hom, eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
