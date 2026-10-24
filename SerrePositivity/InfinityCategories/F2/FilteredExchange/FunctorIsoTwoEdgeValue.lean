module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoTriangleValueBoundary

/-!
概要：元の二辺の値比較を、同じ三頂点を持つ一つの指定合成として保持する。
方針：最後辺・第一辺の順を固定し、三角形境界式の最初の二因子を取り出す。
規約：元の二つの指定値を保持し、結合表示だけを揃える。
使われ方：Ncomp の値式と元の四因子境界式の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A B C X Y Z : SSet.{u}}
  (a : A ⟶ B) (b : B ⟶ C) (v₀ : A ⟶ X) (v₁ : B ⟶ Y) (v₂ : C ⟶ Z)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  (e₀₁ : FunctorIso (a ≫ v₁) (v₀ ≫ f)) (e₁₂ : FunctorIso (b ≫ v₂) (v₁ ≫ g))

/-- 概要：二辺の元の指定値の合成。方針：最後辺・第一辺の順に結合を揃える。
規約：指定因子を保持。使われ方：元の二辺評価の実表示。 -/
def functorIsoTwoEdgeValue : FunctorIso ((a ≫ b) ≫ v₂) (v₀ ≫ (f ≫ g)) :=
  functorIsoOfEq (e₁₂.precomp a) (Category.assoc a b v₂).symm
      (Category.assoc a v₁ g).symm ≪≫
    functorIsoOfEq (e₀₁.postcomp g) rfl (Category.assoc v₀ f g)

variable (d : A ⟶ C) (h : X ⟶ Z)
  (e₀₂ : FunctorIso (d ≫ v₂) (v₀ ≫ h)) (τ : FunctorIso h (f ≫ g))

/-- 概要：四因子境界式の同じ二辺因子を回収。方針：既存の定義を束ねる。
規約：元の三角形と長辺も保持。使われ方：値の消去後に境界式へ戻す。 -/
lemma functorIsoTriangleValueBoundary_eq_twoEdge :
    functorIsoTriangleValueBoundary a b d v₀ v₁ v₂ f g h e₀₁ e₁₂ e₀₂ τ =
      functorIsoTwoEdgeValue a b v₀ v₁ v₂ f g e₀₁ e₁₂ ≪≫
        FunctorIso.precomp τ.symm v₀ ≪≫ e₀₂.symm := by
  simp only [functorIsoTriangleValueBoundary, functorIsoTwoEdgeValue, Iso.trans_assoc]

/-- 概要：長辺因子の消去後も同じ二辺因子を回収。方針：既存の消去式を使用。
規約：指定因子を保つ。使われ方：長辺評価比較と二辺評価比較の照合。 -/
lemma functorIsoTriangleValueBoundary_twoEdge_cancel :
    functorIsoTriangleValueBoundary a b d v₀ v₁ v₂ f g h e₀₁ e₁₂ e₀₂ τ ≪≫ e₀₂ =
      functorIsoTwoEdgeValue a b v₀ v₁ v₂ f g e₀₁ e₁₂ ≪≫
        FunctorIso.precomp τ.symm v₀ := by
  simpa only [functorIsoTwoEdgeValue, Iso.trans_assoc] using
    functorIsoTriangleValueBoundary_long_cancel a b d v₀ v₁ v₂ f g h e₀₁ e₁₂ e₀₂ τ

end SerrePositivity.InfinityCategories.F2
