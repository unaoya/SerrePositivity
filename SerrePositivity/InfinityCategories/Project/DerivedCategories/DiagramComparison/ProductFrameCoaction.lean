module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductParameterCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter

/-!
概要：元の積 frame に、標準単体の鎖への自然な余作用を入れる。
方針：各パラメータで指定グラフと AW を使い、両図式への自然性を適用する。
規約：同じ自由鎖パラメータを使い、単位則は別に検証する。
使われ方：HA 1.2.4、IS-W2 §73 A04。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{u}) (φ : simplicialRingCoefficient.{u} →+* A)
/-- 係数環の宇宙に固定した既存の標準単体パラメータ。 -/
abbrev standardParameterForCoefficients (_A : Type u) (J : Type v) [Category.{w} J] :
    SimplexCategory ⥤ (J ⥤ SSet.{u}) := liftedStandardSimplexParameter J
local notation "P" => standardParameterForCoefficients A J

/-- 積frameの、同じ標準単体鎖への全余単体で自然な余作用。 -/
def productFrameCoaction :
    freeProductFrame A W P ⟶ freeProductFrame A W P ⊗
      (P ⋙ freeNegativeChainsDiagramFunctor A J) where
  app n := freeProductParameterCoaction φ W ((P).obj n)
  naturality := by
    intro n m f
    change (freeNegativeChainsDiagramFunctor A J).map (W ◁ (P).map f) ≫
      freeProductParameterCoaction φ W ((P).obj m) =
        freeProductParameterCoaction φ W ((P).obj n) ≫
          ((freeNegativeChainsDiagramFunctor A J).map (W ◁ (P).map f) ⊗ₘ
            (freeNegativeChainsDiagramFunctor A J).map ((P).map f))
    have h := freeProductParameterCoaction_naturality φ (𝟙 W) ((P).map f)
    simpa only [id_tensorHom] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
