module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparison
/-!
概要：元の重み射を自由積・自由テンソルframeの射へ送る。
方針：同じ自由鎖関手とテンソルの射作用を使い、指定AWの自然性を束ねる。
規約：A11の証明分割。元の指定比較と全単体作用素を保持する。
使われ方：HA 1.2.4、指定Hom比較の重み変数の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable {W W' : J ⥤ SSet.{u}} (a : W' ⟶ W) (P : SimplexCategory ⥤ J ⥤ SSet.{u})
local notation "N" => freeNegativeChainsDiagramFunctor A J
/-- 重みの同じ射を自由積frameの全余単体射にする。 -/
def freeProductFrameWeightMap : freeProductFrame A W' P ⟶ freeProductFrame A W P where
  app n := (N).map (a ▷ P.obj n)
  naturality n m f := by
    change (N).map (W' ◁ P.map f) ≫ (N).map (a ▷ P.obj m) =
      (N).map (a ▷ P.obj n) ≫ (N).map (W ◁ P.map f)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, whisker_exchange]
/-- 重みの同じ射を自由テンソルframeの全余単体射にする。 -/
def freeTensorFrameWeightMap : freeTensorFrame A W' P ⟶ freeTensorFrame A W P where
  app n := (N).map a ▷ (N).obj (P.obj n)
  naturality n m f := by
    change ((N).obj W' ◁ (N).map (P.map f)) ≫ ((N).map a ▷ (N).obj (P.obj m)) =
      ((N).map a ▷ (N).obj (P.obj n)) ≫ ((N).obj W ◁ (N).map (P.map f))
    exact whisker_exchange _ _
/-- 指定AW比較は重みの同じ全射と可換。 -/
theorem freeProductFrameAW_weight_naturality (φ : simplicialRingCoefficient.{u} →+* A) :
    freeProductFrameWeightMap A a P ≫ freeProductFrameAW A W P φ =
      freeProductFrameAW A W' P φ ≫ freeTensorFrameWeightMap A a P := by
  apply NatTrans.ext
  funext n
  have h := freeProductDiagramAW_naturality φ a (𝟙 (P.obj n))
  change (N).map (a ▷ P.obj n) ≫ freeProductDiagramAW φ W (P.obj n) =
    freeProductDiagramAW φ W' (P.obj n) ≫ ((N).map a ▷ (N).obj (P.obj n))
  change (N).map (a ⊗ₘ 𝟙 (P.obj n)) ≫ freeProductDiagramAW φ W (P.obj n) =
    freeProductDiagramAW φ W' (P.obj n) ≫ ((N).map a ⊗ₘ (N).map (𝟙 (P.obj n))) at h
  erw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
  exact h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
