module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoTwoEdgeValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoPrecompNormalizedReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport
/-!
概要：任意の全初期値における二辺値を、同じ最後辺値と第一辺値の二因子へ戻す。
方針：元の指定値の前後合成を保持し、共有する中間の結合表示を明示する。
規約：元の二辺と全係数を変更しない。
使われ方：Ncomp の raw 二辺因子と最後辺の値正方形の接続。
-/

@[expose] public section
open CategoryTheory SSet
noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B C X Y Z K : SSet.{u}}
/-- 概要：元の辺値を同じ全初期値で読む表示。方針：同じ前後合成の端点表示を揃える。
規約：指定値を保持。使われ方：全初期値での raw 二辺因子の回収。 -/
def functorIsoEdgeValueAt (b : B ⟶ C) (v₁ : B ⟶ Y) (v₂ : C ⟶ Z) (g : Y ⟶ Z)
    (e₁₂ : FunctorIso (b ≫ v₂) (v₁ ≫ g)) (p : K ⟶ B) :
    FunctorIso ((p ≫ b) ≫ v₂) (p ≫ (v₁ ≫ g)) :=
  functorIsoOfEq (e₁₂.precomp p) (Category.assoc p b v₂).symm rfl
/-- 概要：元の第一辺値を同じ全初期値と最後射で読む表示。方針：同じ前後合成の端点表示を揃える。
規約：指定値を保持。使われ方：全初期値での raw 二辺因子の回収。 -/
def functorIsoEdgeValuePostAt (a : A ⟶ B) (v₀ : A ⟶ X) (v₁ : B ⟶ Y) (f : X ⟶ Y)
    (e₀₁ : FunctorIso (a ≫ v₁) (v₀ ≫ f)) (q : K ⟶ A) (g : Y ⟶ Z) :
    FunctorIso ((q ≫ a) ≫ (v₁ ≫ g)) (q ≫ (v₀ ≫ (f ≫ g))) :=
  functorIsoOfEq ((e₀₁.precomp q).postcomp g)
    (by simp only [Category.assoc]) (by simp only [Category.assoc])
/-- 概要：元の二辺値は同じ指定最後辺値・第一辺値の順の二因子。方針：同じ前後合成の端点表示を揃える。
規約：指定値を保持。使われ方：全初期値での raw 二辺因子の回収。 -/
lemma functorIsoTwoEdgeValue_precomp_eq_factors
    (a : A ⟶ B) (b : B ⟶ C) (v₀ : A ⟶ X) (v₁ : B ⟶ Y) (v₂ : C ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₀₁ : FunctorIso (a ≫ v₁) (v₀ ≫ f)) (e₁₂ : FunctorIso (b ≫ v₂) (v₁ ≫ g))
    (q : K ⟶ A) :
    functorIsoOfEq ((functorIsoTwoEdgeValue a b v₀ v₁ v₂ f g e₀₁ e₁₂).precomp q)
      (by simp only [Category.assoc]) rfl =
    functorIsoEdgeValueAt b v₁ v₂ g e₁₂ (q ≫ a) ≪≫
      functorIsoEdgeValuePostAt a v₀ v₁ f e₀₁ q g := by
  let E := functorIsoOfEq (e₁₂.precomp a) (Category.assoc a b v₂).symm
    (Category.assoc a v₁ g).symm
  let F := functorIsoOfEq (e₀₁.postcomp g) rfl (Category.assoc v₀ f g)
  have h₁ : HEq (E.precomp q) (functorIsoEdgeValueAt b v₁ v₂ g e₁₂ (q ≫ a)) :=
    functorIsoOfEq_precomp_reindex_heq e₁₂ a q (Category.assoc a b v₂).symm
      (Category.assoc a v₁ g).symm (Category.assoc (q ≫ a) b v₂).symm rfl
  have h₂ : HEq (F.precomp q) (functorIsoEdgeValuePostAt a v₀ v₁ f e₀₁ q g) :=
    (functorIsoOfEq_precomp_heq (e₀₁.postcomp g) rfl (Category.assoc v₀ f g) q).trans
      ((heq_of_eq (functorIso_precomp_postcomp e₀₁ q g).symm).trans
        (functorIsoOfEq_heq _ _ _).symm)
  have hs : q ≫ ((a ≫ b) ≫ v₂) = ((q ≫ a) ≫ b) ≫ v₂ := by
    simp only [Category.assoc]
  have hm : q ≫ ((a ≫ v₁) ≫ g) = (q ≫ a) ≫ (v₁ ≫ g) := by
    simp only [Category.assoc]
  have ht := vertexIso_trans_heq_of_heq (E.precomp q) (F.precomp q)
    (functorIsoEdgeValueAt b v₁ v₂ g e₁₂ (q ≫ a))
    (functorIsoEdgeValuePostAt a v₀ v₁ f e₀₁ q g)
    (congrArg functorVertex hs) (congrArg functorVertex hm) rfl h₁ h₂
  have he := functorIsoOfEq_heq ((functorIsoTwoEdgeValue a b v₀ v₁ v₂ f g e₀₁ e₁₂).precomp q) hs rfl
  have hc : HEq ((functorIsoTwoEdgeValue a b v₀ v₁ v₂ f g e₀₁ e₁₂).precomp q)
      (E.precomp q ≪≫ F.precomp q) := heq_of_eq (functorIso_precomp_trans E F q)
  exact eq_of_heq (he.trans (hc.trans ht))
end SerrePositivity.InfinityCategories.F2
