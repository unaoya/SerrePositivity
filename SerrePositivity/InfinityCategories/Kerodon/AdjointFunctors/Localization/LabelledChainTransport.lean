module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedVertexChainCoordinates
/-!
# 隣接 Hom と両ラベルの元の端点移送

概要：頂点列の表示の等式による全因子の移送を元の Hom の共役と係数作用で回収する。
方針：同じ元の射列の全単射と端点等式を使う。
規約：全作用素と長さ零を保持する。
使われ方：DK10.6(ii)の元の固定頂点列ごとの因子の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite
variable {C : Type u} [Category.{u} C] (A : Cᵒᵖ ⥤ Type u) (B : C ⥤ Type u) {k : ℕ}
lemma cast_fiber {x y : Fin (k + 1) → C} (h : ∀ i, x i = y i) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.Fiber A B k x) :
    cast (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LabelledChainCoordinates.Fiber A B k) (funext h)) v =
      ((fun i => eqToHom (h i.castSucc).symm ≫ v.1 i ≫ eqToHom (h i.succ)),
        A.map (eqToHom (congrArg op (h (Fin.last k)))) v.2.1,
        B.map (eqToHom (h 0)) v.2.2) := by
  obtain rfl := funext h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id, types_id_apply]
  rfl
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
