module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyHomotopy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationVertex

/-!
概要：指定 native 余錐を頂点ホモロジー図式の通常の余錐へ送る。
方針：余錐の全単体ホモトピーとホモトピー圏の自然変換を使う。
規約：余錐の終点は元の実加群の評価ホモロジー。
使われ方：分解の augmentation と filtered ホモロジー余極限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]

lemma dgCoherentConstantHomology_map
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌) (x : D) (q : ℤ) {i j : J} (f : i ⟶ j) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
      (SSet.const y : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _) x q).map f =
        𝟙 _ := by
  let e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, max (u + 1) v} (X := nerve J)
    (CategoryTheory.nerve.edgeMk f).toTruncated).map
      ((SSet.truncation 2).map (SSet.const y))
  have he : e = SSet.Truncated.Edge.id (X := (SSet.truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0) := by
    apply SSet.Truncated.Edge.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1 = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one y
  change (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyHomology R D x q).map
    ((moduleToHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) = _
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeClosed_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

def dgCoherentConstantHomologyIso
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌) (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D
      (SSet.const y : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _) x q ≅
        (Functor.const J).obj (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y).obj
          (Opposite.op x)).homology q) :=
  NatIso.ofComponents (fun j => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D (SSet.const y) x q j)
    (by intro i j f; rw [dgCoherentConstantHomology_map]; simp only [Functor.const_obj_map,
      Category.id_comp, Category.comp_id]; rfl)

variable (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentCoconeHomology (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (x : D) (q : ℤ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q) where
  pt := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) c.vertex).obj (Opposite.op x)).homology q
  ι := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyHomotopy R D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c) x q ≫
    (dgCoherentConstantHomologyIso R D c.vertex x q).hom

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
