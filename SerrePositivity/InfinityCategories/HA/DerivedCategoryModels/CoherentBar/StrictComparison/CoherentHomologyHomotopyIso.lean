module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopyComponent
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：各垂直辺が擬同型である coherent ホモトピーは頂点ホモロジーの自然同型を与える。
方針：指定された成分公式と両端の評価ホモロジー同型で可逆性を判定する。
規約：同じ augmentation の全関手上の自然性を保持する。
使われ方：分解済み coherent 図式の filtered ホモロジー余極限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  {G H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)}

lemma dgCoherentBarHomologyHomotopy_isIso (h : SSet.Homotopy G H)
    (hW : ∀ j : J, moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge h (ULift.up (nerveEquiv.symm j))).toTruncated))
    (x : D) (q : ℤ) : IsIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy R D h x q) := by
  letI (j : J) : IsIso ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy R D h x q).app j) := by
    let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge h (ULift.up (nerveEquiv.symm j))).toTruncated
    letI : QuasiIso ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map f) := hW j x
    letI : IsIso (HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map f) q) :=
      (_root_.quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
    have he : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy R D h x q).app j =
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D G x q j).hom ≫
          HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map f) q ≫
            (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D H x q j).inv := by
      rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy_app,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

def dgCoherentBarHomologyHomotopyIso (h : SSet.Homotopy G H)
    (hW : ∀ j : J, moduleQuasiIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge h (ULift.up (nerveEquiv.symm j))).toTruncated))
    (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q ≅ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D H x q := by
  letI := dgCoherentBarHomologyHomotopy_isIso R D h hW x q
  exact asIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy R D h x q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
