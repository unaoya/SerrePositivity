module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction

/-!
概要：テンソルframeの第二因子に、指定AW対角によるパラメータ余作用を入れる。
方針：同じ自由鎖の対角を全余単体で束ね、結合子で括弧を移す。
規約：指定された正規化パラメータとAWを使う。単位則は別工程。
使われ方：HA 1.2.4、IS-W2 §73 A04。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{u}) (φ : simplicialRingCoefficient.{u} →+* A)
local notation "P" => standardParameterForCoefficients A J
local notation "N" => freeNegativeChainsDiagramFunctor A J

/-- テンソルframeの第二因子の対角を、全パラメータで束ねた余作用。 -/
def tensorFrameCoaction :
    freeTensorFrame A W P ⟶ freeTensorFrame A W P ⊗ (P ⋙ N) := by
  let d : P ⋙ N ⟶ (P ⋙ N) ⊗ (P ⋙ N) := {
    app n := (N).map (lift (𝟙 ((P).obj n)) (𝟙 ((P).obj n))) ≫
      freeProductDiagramAW φ ((P).obj n) ((P).obj n)
    naturality := by
      intro n m f
      change (N).map ((P).map f) ≫ ((N).map (lift (𝟙 _) (𝟙 _)) ≫ _) =
        ((N).map (lift (𝟙 _) (𝟙 _)) ≫ _) ≫
          ((N).map ((P).map f) ⊗ₘ (N).map ((P).map f))
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
      have hg : (P).map f ≫ lift (𝟙 _) (𝟙 _) =
          lift (𝟙 _) (𝟙 _) ≫ ((P).map f ⊗ₘ (P).map f) := by
        simp only [comp_lift, Category.comp_id, lift_map, Category.id_comp]
      rw [hg, CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [freeNegativeChainsDiagramFunctor_map]
      rw [freeProductDiagramAW_naturality]
      simp only [Category.assoc] }
  exact {
    app n := (freeNegativeChainsDiagram (A := A) W ◁ d.app n) ≫ (α_ _ _ _).inv
    naturality := by
      intro n m f
      let B := freeNegativeChainsDiagram (A := A) W
      let g := (N).map ((P).map f)
      change (B ◁ g) ≫ ((B ◁ d.app m) ≫ (α_ _ _ _).inv) =
        ((B ◁ d.app n) ≫ (α_ _ _ _).inv) ≫ ((B ◁ g) ⊗ₘ g)
      have hd : g ≫ d.app m = d.app n ≫ (g ⊗ₘ g) := d.naturality f
      rw [← Category.assoc, ← whiskerLeft_comp, hd, whiskerLeft_comp, Category.assoc]
      have ha := associator_inv_naturality (𝟙 B) g g
      simpa only [Functor.comp_obj, id_tensorHom, Category.assoc] using
        congrArg (fun k => (B ◁ d.app n) ≫ k) ha }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
