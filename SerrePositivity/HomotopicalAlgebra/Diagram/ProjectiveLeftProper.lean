module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
public import SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper

/-! # Left properness of the actual projective diagram model

Projective cofibrations are objectwise cofibrations, and evaluation
preserves actual pushouts. Original left properness therefore suffices.
No left properness of a localized model is assumed.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

lemma leftProper :
    let := modelCategory K I J
    (weakEquivalences (K ⥤ C)).IsStableUnderCobaseChangeAgainst (cofibrations (K ⥤ C)) := by
  let := modelCategory K I J
  constructor
  intro A B f hf
  constructor
  intro Z W f' g' g sq hg k
  exact Quillen.weakEquivalence_of_pushout_along_cofibration
    (sq.map ((CategoryTheory.evaluation K C).obj k))
    (cofibrations_le_objectwise K I J f hf k) (hg k)

end SerrePositivity.DiagramModel.Projective

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.8.4" (partial := component) "仮定：K 小さい、A は Mathlib locally presentable かつ cofibrantly generated、左固有な抽象モデル圏（HTT の左固有部分と一致）。結論：実際に構成した projective model の W が projective cofibration に沿う pushout を保つ。原典の projective-left-proper の部分は一致、injective と right-proper の残る三つの部分は含まない。"] _root_.SerrePositivity.DiagramModel.Projective.leftProper
