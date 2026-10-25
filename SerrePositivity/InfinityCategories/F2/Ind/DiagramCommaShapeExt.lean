module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaGluing

/-!
概要：形状 pushout の元の両部分への制限は、元の diagram comma の全族を決定する。
方針：C 全族と全円柱のそれぞれで元の積 pushout の一意性を使う。
規約：同型による置換でなく元の全射の等号を結論する。
使われ方：貼った全余錐が元の q 自身を旧族で回収することの検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の形状 pushout の両制限が一致する全 comma 族は同じ元の全族。
方針：元の二全成分で pushout の一意性。規約：全射の等号。使われ方：旧族の回収。 -/
lemma diagramComma_shape_ext (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    {J K₁ K₂ K : SSet.{u}} {i : J ⟶ K₁} {j : J ⟶ K₂}
    {r : K₁ ⟶ K} {s : K₂ ⟶ K} (h : IsPushout i j r s)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    {T : SSet.{u + 1}} (q q' : T ⟶ diagramComma κ D)
    (h₁ : q ≫ diagramCommaRestriction κ D r = q' ≫ diagramCommaRestriction κ D r)
    (h₂ : q ≫ diagramCommaRestriction κ D s = q' ≫ diagramCommaRestriction κ D s) : q = q' := by
  apply diagramComma_rightFamily_ext κ D
  · apply (tensorShape_isPushout h T).hom_ext
    · rw [diagramCommaOriginalFamily_restrict, diagramCommaOriginalFamily_restrict, h₁]
    · rw [diagramCommaOriginalFamily_restrict, diagramCommaOriginalFamily_restrict, h₂]
  · apply (tensorShape_isPushout h (join T (Δ[0] : SSet.{u + 1}))).hom_ext
    · rw [diagramCommaRightPrism_restrict, diagramCommaRightPrism_restrict, h₁]
    · rw [diagramCommaRightPrism_restrict, diagramCommaRightPrism_restrict, h₂]
end SerrePositivity.InfinityCategories.F2.Ind
