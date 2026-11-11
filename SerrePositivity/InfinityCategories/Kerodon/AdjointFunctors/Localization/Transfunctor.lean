module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.EqToHom

/-!
# 元の Grothendieck 圏上の transfunctor と次数ごとの作用

概要：DK10.1の covariant transfunctor を元の Grothendieck 圏からの通常の関手で表す。
方針：元の fiber 包含と標準の底の射の自然変換を関手で送る。
規約：全作用素を持ち、恒等・合成の端点移送を異種等式で明示する。
使われ方：DK10.2の単体的な二方向 Grothendieck 構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor
open CategoryTheory
variable {I : Type v} [Category I] (B : I ⥤ Cat.{u, u})
abbrev Covariant := Grothendieck B ⥤ Cat.{u, u}
variable {B} (T : Covariant B)
def fiber (i : I) : B.obj i ⥤ Cat.{u, u} := Grothendieck.ι B i ⋙ T
def transition {i j : I} (θ : i ⟶ j) : fiber T i ⟶ (B.map θ).toFunctor ⋙ fiber T j :=
  Functor.whiskerRight (Grothendieck.ιNatTrans (F := B) θ) T

lemma transition_id_app (i : I) (x : B.obj i) :
    HEq ((transition T (𝟙 i)).app x) (𝟙 ((fiber T i).obj x)) := by
  change HEq (T.map ((Grothendieck.ιNatTrans (F := B) (𝟙 i)).app x)) _
  have h : (Grothendieck.ιNatTrans (F := B) (𝟙 i)).app x =
      eqToHom (show (Grothendieck.ι B i).obj x =
        (Grothendieck.ι B i).obj ((B.map (𝟙 i)).toFunctor.obj x) by
          simp only [B.map_id]; rfl) := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [Grothendieck.ιNatTrans, Grothendieck.base_eqToHom]
      rfl
    · dsimp [Grothendieck.ιNatTrans]
      rw [Grothendieck.fiber_eqToHom]
      simp only [Category.comp_id]
  rw [h, eqToHom_map]
  exact eqToHom_heq_id_dom _ _ _
lemma transition_comp_app {i j k : I} (θ : i ⟶ j) (φ : j ⟶ k) (x : B.obj i) :
    HEq ((transition T (θ ≫ φ)).app x)
      ((transition T θ).app x ≫
        (transition T φ).app ((B.map θ).toFunctor.obj x)) := by
  have h : (Grothendieck.ιNatTrans (F := B) (θ ≫ φ)).app x =
      (Grothendieck.ιNatTrans (F := B) θ).app x ≫
        (Grothendieck.ιNatTrans (F := B) φ).app ((B.map θ).toFunctor.obj x) ≫
          eqToHom (show (Grothendieck.ι B k).obj
            ((B.map φ).toFunctor.obj ((B.map θ).toFunctor.obj x)) =
              (Grothendieck.ι B k).obj ((B.map (θ ≫ φ)).toFunctor.obj x) by
                rw [B.map_comp]; rfl) := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [Grothendieck.ιNatTrans, Grothendieck.comp_base,
        Grothendieck.base_eqToHom]
      change θ ≫ φ = θ ≫ φ ≫ 𝟙 k
      simp only [Category.comp_id]
    · dsimp [Grothendieck.ιNatTrans]
      simp only [Grothendieck.fiber_eqToHom, Functor.map_id, Category.comp_id,
        Category.id_comp, eqToHom_trans]
  change HEq (T.map ((Grothendieck.ιNatTrans (F := B) (θ ≫ φ)).app x)) _
  rw [h, T.map_comp, T.map_comp, eqToHom_map]
  rw [← Category.assoc]
  exact comp_eqToHom_heq _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor
