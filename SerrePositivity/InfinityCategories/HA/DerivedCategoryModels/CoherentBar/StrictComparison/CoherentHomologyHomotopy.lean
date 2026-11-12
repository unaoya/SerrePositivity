module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans

/-!
概要：全単体ホモトピーは coherent 図式の頂点ホモロジー図式の自然変換を与える。
方針：元のホモトピー圏の自然変換を添字と評価ホモロジーで前後合成する。
規約：高次 HA データを捨てて strict 化しない。
使われ方：実分解の augmentation によるホモロジー図式の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  {G H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)}

lemma dgBarPathToEdge_homMk {Y : SSet.{w}} [Quasicategory Y]
    {a b : Y _⦋0⦌} (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj Y) a b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk e := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk]

def dgBarHomotopyNatTrans₂ {X Y : SSet.{w}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map g := by
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints h.h h.h₀ h.h₁
  refine
    { app a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
        (η.app (SSet.HomotopyCategory.mk a.pt))
      naturality := ?_ }
  rintro a b ⟨e⟩
  have hn := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).congr_map
    (η.naturality (SSet.Truncated.HomotopyCategory.homMk e))
  simp only [Functor.map_comp] at hn
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk (e.map ((SSet.truncation 2).map f))) ≫ _ =
    _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk (e.map ((SSet.truncation 2).map g))) at hn
  rw [dgBarPathToEdge_homMk, dgBarPathToEdge_homMk] at hn
  exact hn

def dgCoherentBarHomologyHomotopy (h : SSet.Homotopy G H) (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x q ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D H x q := by
  exact Functor.whiskerRight
    (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarIndexHomotopyFunctor J) (dgBarHomotopyNatTrans₂ h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R (RightModule R D) ⋙ moduleHomotopyHomology R D x q)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
