module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
概要：積重みのパラメータを複製し、指定 AW による鎖の余作用を作る。
方針：積の第二射影のグラフを自由鎖へ送り、元の AW と合成する。
規約：重みとパラメータの全図式射に自然。単位則とホモトピーの輸送は後続。
使われ方：HA 1.2.4、G10 の鎖ホモトピーを単体パラメータで評価する入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {A : Type u} [CommRing A]

/-- 第二パラメータを複製する元のグラフ。 -/
def productParameterGraph (X Y : J ⥤ SSet.{u}) : X ⊗ Y ⟶ (X ⊗ Y) ⊗ Y :=
  lift (𝟙 _) (snd X Y)

/-- 同じグラフは重みとパラメータの全射に自然。 -/
theorem productParameterGraph_naturality {X X' Y Y' : J ⥤ SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ productParameterGraph X' Y' =
      productParameterGraph X Y ≫ ((f ⊗ₘ g) ⊗ₘ g) := by
  simp only [productParameterGraph, comp_lift, Category.comp_id, lift_map,
    Category.id_comp, tensorHom_snd]

/-- 元の自由積鎖から、同じ鎖とパラメータ鎖とのテンソルへの指定余作用。 -/
def freeProductParameterCoaction (φ : simplicialRingCoefficient.{u} →+* A)
    (X Y : J ⥤ SSet.{u}) :
    freeNegativeChainsDiagram (A := A) (X ⊗ Y) ⟶
      freeNegativeChainsDiagram (A := A) (X ⊗ Y) ⊗ freeNegativeChainsDiagram (A := A) Y :=
  (freeNegativeChainsDiagramFunctor A J).map (productParameterGraph X Y) ≫
    freeProductDiagramAW φ (X ⊗ Y) Y

/-- 指定余作用の全図式射への自然性。 -/
@[reassoc]
theorem freeProductParameterCoaction_naturality (φ : simplicialRingCoefficient.{u} →+* A)
    {X X' Y Y' : J ⥤ SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (freeNegativeChainsDiagramFunctor A J).map (f ⊗ₘ g) ≫
        freeProductParameterCoaction φ X' Y' =
      freeProductParameterCoaction φ X Y ≫
        ((freeNegativeChainsDiagramFunctor A J).map (f ⊗ₘ g) ⊗ₘ
          (freeNegativeChainsDiagramFunctor A J).map g) := by
  dsimp only [freeProductParameterCoaction]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    productParameterGraph_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [freeNegativeChainsDiagramFunctor_map]
  rw [freeProductDiagramAW_naturality]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
