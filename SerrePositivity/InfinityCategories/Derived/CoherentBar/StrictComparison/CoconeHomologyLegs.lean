module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoconeVertexRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexInclusion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ClosedEdgeRecovery
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCoconeHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyHomotopyComponent
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgBarCoconeVertexModuleMap_edge (c : JoinCocone G) (s : I _⦋0⦌) :
    dgBarCoconeVertexModuleMap R D G c s =
      eqToHom (congrArg (ForgetEnrichment.of (Complex R)) (dgCoherentBarSource_vertex R D G s)) ≫
        DGNerve.HomotopyComparison.edgeClosed
          (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c) (ULift.up s)).toTruncated := by
  rw [dgBarCoconeVertexModuleMap_eq]
  have he : (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c)
      (ULift.up s)).edge = dgCoherentBarCoconeSimplex R D G c s :=
    F2.Compact.coconeHomotopyLeg_edge c (ULift.up s)
  have h := dgBarEdgeClosed_recover_transport R D
    (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c) (ULift.up s)).toTruncated he
    (dgCoherentBarCoconeSimplex_source R D G c s) (dgCoherentBarCoconeSimplex_last R D G c s)
    (dgCoherentBarSource_vertex R D G s) rfl
  simpa only [eqToHom_refl, Category.comp_id] using! h

variable {J : Type u} [PartialOrder J]
  (H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgNerve R (RightModule R D))

lemma dgCoherentCoconeHomology_leg (c : JoinCocone H) (x : D) (q : ℤ) (j : J) :
    (dgCoherentCoconeHomology R D H c x q).ι.app j =
      (dgCoherentBarHomologyDiagramObjIso R D H x q j).hom ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
          (DGNerve.HomotopyComparison.edgeClosed
            (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c)
              (ULift.up (nerveEquiv.symm j))).toTruncated)) q := by
  change (moduleHomotopyHomology R D x q).map
      ((DGNerve.HomotopyComparison.toH0 R (RightModule R D)).map
        ((dgBarHomotopyNatTrans₂ (F2.coconeTransformationHomotopy c)).app
          ⟨ULift.up (nerveEquiv.symm j)⟩)) ≫ _ = _
  rw [dgBarHomotopyNatTrans₂_app, DGNerve.HomotopyComparison.toH0_homMk]
  exact (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).hom.naturality
    ((moduleEvaluation R D x).map
      (DGNerve.HomotopyComparison.edgeClosed
        (simplicialHomotopyVertexEdge (F2.coconeTransformationHomotopy c)
          (ULift.up (nerveEquiv.symm j))).toTruncated))

lemma dgCoherentCoconeHomology_source_leg (c : JoinCocone H) (x : D) (q : ℤ)
    (s : (nerve J) _⦋0⦌) :
    (dgCoherentBarSourceHomologyIso R D H x q 0 s).hom ≫
        (dgCoherentCoconeHomology R D H c x q).ι.app (s.obj 0) =
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
        (dgBarCoconeVertexModuleMap R D H c s)) q := by
  obtain ⟨j, rfl⟩ := (nerveEquiv (C := J)).symm.surjective s
  rw [dgCoherentCoconeHomology_leg, dgBarCoconeVertexModuleMap_edge,
    Functor.map_comp, HomologicalComplex.homologyMap_comp]
  simp only [dgCoherentBarSourceHomologyIso, dgCoherentBarVertexHomologyTransportIso,
    Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    Functor.mapIso_hom, eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.InfinityCategories
