module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyCategory
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：元の coherent 図式から各評価・各次数のホモロジー図式を作る。
方針：元の辺と HA 三角形をホモトピー圏へ送り、その後にホモロジーを取る。
規約：bar の入力 G は高次成分を含む元の図式のままである。
使われ方：単体次元フィルトレーションの最初のホモロジーと filtered 余極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

/-- 元の射と合成三角形を、持ち上げた nerve の辺の類へ送る。 -/
def dgCoherentBarIndexHomotopyFunctor (J : Type u) [Category.{u} J] :
    J ⥤ SSet.Truncated.HomotopyCategory₂
      ((SSet.truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj (nerve J))) where
  obj j := ⟨ULift.up (nerveEquiv.symm j)⟩
  map {i j} f := SSet.Truncated.HomotopyCategory₂.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, v} (X := nerve J)
      ((CategoryTheory.nerve.edgeMk (x := i) (y := j) f).toTruncated))
  map_id j := by
    rw [CategoryTheory.nerve.edgeMk_id, SSet.Edge.toTruncated_id]
    rfl
  map_comp f g := by
    change SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, v} (X := nerve J) (CategoryTheory.nerve.edgeMk (f ≫ g)).toTruncated) =
      SSet.Truncated.HomotopyCategory₂.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, v} (X := nerve J) (CategoryTheory.nerve.edgeMk f).toTruncated) ≫
      SSet.Truncated.HomotopyCategory₂.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, v} (X := nerve J) (CategoryTheory.nerve.edgeMk g).toTruncated)
    obtain ⟨t⟩ := (CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.upComp.{u, v} (X := nerve J) t.toTruncated).homotopyCategory₂_fac.symm

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

/-- 元の coherent 図式の K(D) における像。strict な持上げは選ばない。 -/
def dgCoherentBarHomotopyDiagram : J ⥤ ModuleHomotopyCategory R D :=
  dgCoherentBarIndexHomotopyFunctor J ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map G ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R (RightModule R D)

/-- 各評価・各次数のホモロジー。高次 HA データは関手法則の証明に使われる。 -/
def dgCoherentBarHomologyDiagram (x : D) (q : ℤ) : J ⥤ ModuleCat R :=
  dgCoherentBarHomotopyDiagram R D G ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyHomology R D x q

def dgCoherentBarHomologyDiagramObjIso (x : D) (q : ℤ) (j : J) :
    (dgCoherentBarHomologyDiagram R D G x q).obj j ≅
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j)).obj (Opposite.op x)).homology q :=
  (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat R) (.up ℤ) q).app
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j)).obj (Opposite.op x))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
