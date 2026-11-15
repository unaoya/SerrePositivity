module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFrames

/-!
概要：元の source frame の零次の対象と、その対象への同じ増大射を取り出す。
方針：単体圏の零単体への一意な射を元の frame に作用させる。
規約：frame を選び直さず、元の図式への増大射との両立を保つ。
使われ方：RR01 の実 source frame を両側 frame の比較へ渡す入口。
対応：Hovey §5.4、HTT 4.2.4.4 の模型比較で使う増大射の計算法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance sourceFrameZeroInitial : HasInitial (StrictComplexDiagram A d) :=
  (isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance sourceFrameZeroModel : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d

/-- 指定 source frame の同じ零次対象。 -/
def strictDiagramSourceFrameZero (X : StrictComplexDiagram A d) : StrictComplexDiagram A d :=
  (strictDiagramSourceFrame A d X).obj.obj (SimplexCategory.mk 0)

/-- 指定 source frame の零次対象は cofibrant。 -/
lemma strictDiagramSourceFrameZero_isCofibrant (X : StrictComplexDiagram A d) :
    IsCofibrant (strictDiagramSourceFrameZero A d X) :=
  (strictDiagramSourceFrame A d X).isCofibrant_obj _

/-- 零単体への潰し写像を、同じ frame に作用させた増大射。 -/
def strictDiagramSourceFrameZeroAugmentation (X : StrictComplexDiagram A d) :
    (strictDiagramSourceFrame A d X).obj ⟶
      (Functor.const SimplexCategory).obj (strictDiagramSourceFrameZero A d X) where
  app n := (strictDiagramSourceFrame A d X).obj.map
    (SimplexCategory.const n (SimplexCategory.mk 0) 0)
  naturality n m f := by
    change (strictDiagramSourceFrame A d X).obj.map f ≫
      (strictDiagramSourceFrame A d X).obj.map (SimplexCategory.const m _ 0) =
        (strictDiagramSourceFrame A d X).obj.map (SimplexCategory.const n _ 0) ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    apply congrArg
    ext i
    rfl

/-- 同じ増大射の各成分は frame のホモトピー定値性による弱同値。 -/
lemma strictDiagramSourceFrameZeroAugmentation_weak (X : StrictComplexDiagram A d)
    (n : SimplexCategory) :
    weakEquivalences (StrictComplexDiagram A d)
      ((strictDiagramSourceFrameZeroAugmentation A d X).app n) :=
  (strictDiagramSourceFrame A d X).homotopicallyConstant _

/-- 元の図式への増大射は、零次への同じ増大射を経由する。 -/
lemma strictDiagramSourceFrameZeroAugmentation_fac (X : StrictComplexDiagram A d)
    (n : SimplexCategory) :
    (strictDiagramSourceFrameZeroAugmentation A d X).app n ≫
      (strictDiagramSourceFrame A d X).augmentation.app (SimplexCategory.mk 0) =
        (strictDiagramSourceFrame A d X).augmentation.app n := by
  have h := (strictDiagramSourceFrame A d X).augmentation.naturality
    (SimplexCategory.const n (SimplexCategory.mk 0) 0)
  change (strictDiagramSourceFrameZeroAugmentation A d X).app n ≫
    (strictDiagramSourceFrame A d X).augmentation.app (SimplexCategory.mk 0) =
      (strictDiagramSourceFrame A d X).augmentation.app n ≫ 𝟙 X at h
  exact h.trans (Category.comp_id _)


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
