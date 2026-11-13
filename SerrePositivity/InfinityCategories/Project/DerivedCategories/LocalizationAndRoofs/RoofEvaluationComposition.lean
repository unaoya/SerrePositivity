module
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
概要：四合成関係と三つの評価方程式から評価の合成を得る。
方針：合成分母を消去する。規約：任意の圏とエピな合成分母を扱う。
使われ方：パラメータ関手圏における実屋根評価の比較。
-/
@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 共通対角の四関係と三評価式は、エピな合成分母の消去により評価の合成を定める。 -/
lemma roofEvaluation_comp {C : Type u} [Category.{v} C] {q₀ q₁ q₂ x y z : C}
    (d : q₀ ⟶ q₁) (d₁ : q₁ ⟶ x) (n₁ : q₁ ⟶ y)
    (d₂ : q₂ ⟶ y) (n₂ : q₂ ⟶ z) (l : q₀ ⟶ q₂)
    (dc : q₀ ⟶ x) (nc : q₀ ⟶ z) (h : q₀ ⟶ y) [Epi dc]
    (hd : d ≫ d₁ = dc) (h₁ : d ≫ n₁ = h) (h₂ : l ≫ d₂ = h)
    (hn : l ≫ n₂ = nc) (er : x ⟶ y) (es : y ⟶ z) (ec : x ⟶ z)
    (hr : d₁ ≫ er = n₁) (hs : d₂ ≫ es = n₂) (hc : dc ≫ ec = nc) : er ≫ es = ec := by
  apply (cancel_epi dc).mp
  calc
    _ = d ≫ n₁ ≫ es := by
      rw [← hd]
      simpa only [Category.assoc] using congrArg (fun v => d ≫ v ≫ es) hr
    _ = l ≫ d₂ ≫ es := by rw [← Category.assoc, h₁, ← h₂, Category.assoc]
    _ = nc := by rw [hs, hn]
    _ = _ := hc.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
