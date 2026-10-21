module

public import SerrePositivity.InfinityCategories.F2.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.EmptyCone
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
概要：任意の空形状上の元の錐の極限性は、元の頂点の終対象性と同値。
方針：空部分複体との同型に沿い、slice の頂点射影の厳密な同型を回収する。
規約：元の形状・図式・錐を変更しない。使われ方：filtered 極限交換の空形状の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の空形状上の slice の頂点射影は厳密な同型。 -/
lemma emptyShapeSliceProjection_isIso {K X : SSet.{u}} (hK : ¬ K.Nonempty) (p : K ⟶ X) :
    IsIso (sliceOverProjection p) := by
  let e : K ≅ (⊥ : X.Subcomplex) :=
    (SSet.isInitialOfNotNonempty hK).uniqueUpToIso Subcomplex.isInitialBot
  have hi : e.inv ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  have : IsIso (sliceOverRestrict p e.inv) := sliceOverRestrict_isIso p e.inv
  have : IsIso (normalizedConeRestriction p e.inv hi) := by
    dsimp only [normalizedConeRestriction]
    infer_instance
  rw [← normalizedConeRestriction_projection p e.inv hi]
  infer_instance

/-- 任意の空形状上の元の錐が極限であることと、その頂点の終対象性は同値。 -/
lemma isLimitCone_emptyShape_iff_vertex {K X : SSet.{u}} (hK : ¬ K.Nonempty)
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsTerminalVertex c.vertex := by
  have := emptyShapeSliceProjection_isIso hK p
  constructor
  · intro hc
    exact hc.map_of_isIso (sliceOverProjection p)
  · intro hc
    exact isTerminalVertex_of_trivialKanFibration (sliceOverProjection p) hc

end SerrePositivity.InfinityCategories.F2
