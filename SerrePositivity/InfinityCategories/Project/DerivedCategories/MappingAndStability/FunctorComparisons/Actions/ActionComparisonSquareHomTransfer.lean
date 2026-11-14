module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.Actions.ActionCompositorNaturalityTransfer
/-!
概要：指定比較の自然性から元の合成子の全射自然性を移す。
方針：同じ指定比較と射の値を保持し、全関手圏の等式を照合する。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma comparisonSquare_transfer_hom_naturality {C : Type u} [Category.{v} C]
    {S₀ S₁ T₀ T₁ G₀ G₁ U₀ U₁ : C}
    (x₀ : T₀ ≅ U₀) (x₁ : T₁ ≅ U₁) (n₀ : S₀ ≅ G₀) (n₁ : S₁ ≅ G₁)
    (c₀ : S₀ ≅ T₀) (c₁ : S₁ ≅ T₁)
    (i : S₀ ⟶ S₁) (j : G₀ ⟶ G₁) (t : T₀ ⟶ T₁) (u : U₀ ⟶ U₁)
    (a₀ : G₀ ≅ U₀) (a₁ : G₁ ≅ U₁)
    (hc₀ : c₀ ≪≫ x₀ = n₀ ≪≫ a₀) (hc₁ : c₁ ≪≫ x₁ = n₁ ≪≫ a₁)
    (hn : n₀.hom ≫ j = i ≫ n₁.hom) (hx : x₀.hom ≫ u = t ≫ x₁.hom)
    (ha : a₀.hom ≫ u = j ≫ a₁.hom) : c₀.hom ≫ t = i ≫ c₁.hom := by
  have h₀ : c₀.hom ≫ x₀.hom = n₀.hom ≫ a₀.hom := congrArg Iso.hom hc₀
  have h₁ : c₁.hom ≫ x₁.hom = n₁.hom ≫ a₁.hom := congrArg Iso.hom hc₁
  apply (cancel_mono x₁.hom).mp
  calc
    _ = c₀.hom ≫ (t ≫ x₁.hom) := Category.assoc _ _ _
    _ = c₀.hom ≫ (x₀.hom ≫ u) := by rw [← hx]
    _ = (n₀.hom ≫ a₀.hom) ≫ u := by rw [← Category.assoc, h₀]
    _ = n₀.hom ≫ (j ≫ a₁.hom) := by rw [Category.assoc, ha]
    _ = (i ≫ n₁.hom) ≫ a₁.hom := by rw [← Category.assoc, hn]
    _ = i ≫ (c₁.hom ≫ x₁.hom) := by rw [Category.assoc, ← h₁]
    _ = _ := (Category.assoc _ _ _).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
