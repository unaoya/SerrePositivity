module

public import SerrePositivity.EInfinity.Hammock.ValueSupportSubcomplex

/-!
# 元の有限個の値への制限の弱同値

概要：各 singleton への元の制限が弱同値なら、有限個の値への制限も弱同値。
方針：互いに素な二つの値の集合の部分複体を元の pushout で貼る。
規約：結論は元の全体の射の同じ制限である。
使われ方：元の評価の各 fiber から有限部分の弱同値へ。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ValueSupport
open CategoryTheory SSet SerrePositivity.InfinityCategories

variable {B : Type u} {X Y : SSet.{u}}
  (ℓ : X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  (μ : Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (f : X ⟶ Y) (h : f ≫ μ = ℓ)

lemma finite_restriction_weak
    (hw : ∀ β, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (restriction ℓ μ f h {β})) (S : Finset B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (restriction ℓ μ f h (S : Set B)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact weakMapSubcomplex_of_eq f (A := ⊥) (B := ⊥)
      (by ext n x; simp [subcomplex]) (by ext n x; simp [subcomplex])
      (fun _ _ hx => False.elim hx) (mapsTo ℓ μ f h (∅ : Finset B)) (weakMapSubcomplex_bottom f)
  | @insert β S hβ ih =>
    have hd : Disjoint ({β} : Set B) (S : Set B) := by
      simpa only [Set.disjoint_singleton_left, Finset.mem_coe] using hβ
    have hInf := weakMapSubcomplex_of_eq f
      (subcomplex_disjoint ℓ hd).symm (subcomplex_disjoint μ hd).symm
      (fun _ _ hx => False.elim hx)
      (mapsToSubcomplexInf f (mapsTo ℓ μ f h {β}) (mapsTo ℓ μ f h (S : Set B)))
      (weakMapSubcomplex_bottom f)
    have hu := weakUnion_gluing f (mapsTo ℓ μ f h {β}) (mapsTo ℓ μ f h (S : Set B))
      hInf (hw β) ih
    exact weakMapSubcomplex_of_eq f
      (by rw [← subcomplex_union]; simp only [Finset.coe_insert, Set.singleton_union])
      (by rw [← subcomplex_union]; simp only [Finset.coe_insert, Set.singleton_union])
      (mapsToSubcomplexSup f (mapsTo ℓ μ f h {β}) (mapsTo ℓ μ f h (S : Set B)))
      (mapsTo ℓ μ f h (insert β S : Finset B)) hu

end SerrePositivity.EInfinity.Hammock.ValueSupport
