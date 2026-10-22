module

public import SerrePositivity.InfinityCategories.F1.FatConeParameterPrism
public import SerrePositivity.InfinityCategories.F1.FatJoinTensorExt

/-!
概要：固定頂点の fat 錐の全族は、元の図式の円柱表示で一意に決まる。
方針：左の一点の補充・忘却の同型で全円柱へ戻し、両端固定の外延性を使う。
規約：任意のパラメータを保持する。頂点ごとの単射性へ弱めない。
使われ方：fat 錐と定値始域からの変換の同型の逆則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 元の円柱表示から、左の一点を持つ fat 錐の全円柱を回収する。 -/
lemma fatConeParameterPrism_cylinder (a : T ⟶ fixedEndpointFatConeSpace f z) :
    (fatConeCylinderProjection K ▷ T) ≫ fatConeParameterPrism a =
      (fatJoinCylinder Δ[0] K ▷ T) ≫ uncurry (a ≫ fixedFatConeFamilyEvaluation f z) := by
  rw [fatConeParameterPrism, fatConeCylinderMap, comp_whiskerRight,
    ← Category.assoc, ← Category.assoc, ← comp_whiskerRight, Category.assoc]
  change (((fatConeCylinderIso K).hom ≫ (fatConeCylinderIso K).inv) ▷ T) ≫ _ = _
  rw [Iso.hom_inv_id, id_whiskerRight, Category.id_comp]

/-- 固定両端の全族の円柱表示は単射。 -/
lemma fatConeParameterPrism_injective :
    Function.Injective (fatConeParameterPrism (T := T) (f := f) (z := z)) := by
  intro a b h
  apply vertexFiber_hom_ext
  apply uncurry_injective
  change uncurry (a ≫ fixedFatConeFamilyEvaluation f z) =
    uncurry (b ≫ fixedFatConeFamilyEvaluation f z)
  apply fatJoinTensorRight_hom_ext
  · rw [← fatConeParameterPrism_cylinder, ← fatConeParameterPrism_cylinder, h]
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    simp only [Category.assoc, fixedFatConeFamilyEvaluation, fixedFatConeSpace_inl,
      SSet.comp_const]
  · rw [← uncurry_pre_app, ← uncurry_pre_app]
    simp only [Category.assoc, fixedFatConeFamilyEvaluation, fixedFatConeSpace_inr,
      SSet.comp_const]

end SerrePositivity.InfinityCategories
