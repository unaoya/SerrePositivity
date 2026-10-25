module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyDiagram
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category.{u} J]
  {G H : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D)}

lemma dgBarPathToEdge_homMk {Y : SSet.{w}} [Quasicategory Y]
    {a b : Y _⦋0⦌} (e : SSet.Truncated.Edge (X := (SSet.truncation 2).obj Y) a b) :
    (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk e := by
  simp only [pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk]

def dgBarHomotopyNatTrans₂ {X Y : SSet.{w}}
    [Quasicategory X] [Quasicategory Y] {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    HomotopyCategoryMap.map f ⟶ HomotopyCategoryMap.map g := by
  let η := homotopyNatTransOfEndpoints h.h h.h₀ h.h₁
  refine
    { app a := (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
        (η.app (SSet.HomotopyCategory.mk a.pt))
      naturality := ?_ }
  rintro a b ⟨e⟩
  have hn := (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).congr_map
    (η.naturality (SSet.Truncated.HomotopyCategory.homMk e))
  simp only [Functor.map_comp] at hn
  change (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk (e.map ((SSet.truncation 2).map f))) ≫ _ =
    _ ≫ (pathToEdgeHomotopyCategory ((SSet.truncation 2).obj Y)).map
      (SSet.Truncated.HomotopyCategory.homMk (e.map ((SSet.truncation 2).map g))) at hn
  rw [dgBarPathToEdge_homMk, dgBarPathToEdge_homMk] at hn
  exact hn

def dgCoherentBarHomologyHomotopy (h : SSet.Homotopy G H) (x : D) (q : ℤ) :
    dgCoherentBarHomologyDiagram R D G x q ⟶ dgCoherentBarHomologyDiagram R D H x q := by
  exact Functor.whiskerRight
    (Functor.whiskerLeft (dgCoherentBarIndexHomotopyFunctor J) (dgBarHomotopyNatTrans₂ h))
    (DGNerve.HomotopyComparison.toH0 R (RightModule R D) ⋙ moduleHomotopyHomology R D x q)

end SerrePositivity.InfinityCategories
