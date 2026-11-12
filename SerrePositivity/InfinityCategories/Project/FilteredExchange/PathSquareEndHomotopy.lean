module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy


/-!
概要：指定 path 正方形の終端は、側辺の終点の間の実際の path を与える。
方針：二側辺の終点を取り、時間と path の端点の可換性を使う。
規約：終端の全円柱を選び直さない。
使われ方：path の変形を引き戻し内のホモトピーへまとめる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：側辺と整合する指定正方形の終端を、元の終点間の path として読む。
方針：側辺等式を時間一で制限し、正方形の終端条件を代入する。
規約：h は元の終端の全円柱そのもの。使われ方：引き戻し内の比較の終点。 -/
def pathSquareEndHomotopy {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
    {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
    (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
    {a b : K ⊗ (Δ[1] : SSet.{u}) ⟶ X} (G : SSet.Homotopy a b)
    (h₀ : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = U.h ≫ f)
    (h₁ : ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = V.h ≫ g) :
    SSet.Homotopy (u₁ ≫ f) (v₁ ≫ g) where
  h := b
  h₀ := by
    change SSet.ι₀ ≫ b = u₁ ≫ f
    have h := congrArg (fun r ↦ (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ r) h₀
    change (SSet.ι₀ ≫ SSet.ι₁) ≫ G.h = (SSet.ι₁ ≫ U.h) ≫ f at h
    rw [Category.assoc, G.h₁, U.h₁] at h
    exact h
  h₁ := by
    change SSet.ι₁ ≫ b = v₁ ≫ g
    have h := congrArg (fun r ↦ (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ r) h₁
    change (SSet.ι₁ ≫ SSet.ι₁) ≫ G.h = (SSet.ι₁ ≫ V.h) ≫ g at h
    rw [Category.assoc, G.h₁, V.h₁] at h
    exact h
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
