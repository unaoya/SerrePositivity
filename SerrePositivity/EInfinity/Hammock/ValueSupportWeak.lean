module

public import SerrePositivity.EInfinity.Hammock.ValueSupportDiagram
public import SerrePositivity.EInfinity.Hammock.ValueSupportSingletonWeak
public import SerrePositivity.EInfinity.Hammock.WeakFiniteSubsetColimit

/-!
# 元の離散な値への評価の fiber による弱同値判定

概要：各値への制限が弱同値なら元の射自身も弱同値となる。
方針：有限個の値の貼り合わせと同じ有限部分集合図式の filtered 余極限を使う。
規約：結論は元の射自身であり、始終域の Kan 性を追加しない。
使われ方：元の自由圏の hammock 評価の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ValueSupport
open CategoryTheory Limits SerrePositivity.InfinityCategories

variable {B : Type u} {X Y : SSet.{u}}
  (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (f : X ⟶ Y) (h : f ≫ μ = ℓ)

lemma weak_of_singleton_restrictions
    (hw : ∀ β, IsWeakHomotopyEquivalence (restriction ℓ μ f h {β})) :
    IsWeakHomotopyEquivalence f := by
  have hc : IsWeakHomotopyEquivalence (colim.map (diagramMap ℓ μ f h)) :=
    weakFiniteSubsetColimitMap _ (finite_restriction_weak ℓ μ f h hw)
  have heX := (isPrecompositionEquivalence_of_iso (colimitIso ℓ)).isWeakHomotopyEquivalence
  have heY := (isPrecompositionEquivalence_of_iso (colimitIso μ)).isWeakHomotopyEquivalence
  apply heX.cancel_left
  rw [← colimitIso_naturality ℓ μ f h]
  exact hc.comp heY

lemma weak_of_contractible_fibers
    (hc : ∀ β, IsWeaklyContractible (SimplicialValueFiber.space ℓ β)) :
    IsWeakHomotopyEquivalence ℓ :=
  weak_of_singleton_restrictions ℓ (𝟙 _) ℓ (Category.comp_id ℓ)
    (fun β => singleton_restriction_weak ℓ β (hc β))

end SerrePositivity.EInfinity.Hammock.ValueSupport
