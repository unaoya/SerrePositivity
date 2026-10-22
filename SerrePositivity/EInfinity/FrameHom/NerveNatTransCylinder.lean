module

public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransHomotopy

/-!
# 自然変換の元の円柱の全単体での評価

概要：元の nerve 自然変換ホモトピーを任意次数と任意の時間単体で計算する。
方針：指数比較の評価公式とその自然性を使う。
規約：ホモトピーを選び直さず、同じ全円柱を保持する。
使われ方：roof 円柱の始点変更と語の挿入・縮約の厳密な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet Opposite
open scoped Simplicial
namespace SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories
variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}
lemma nerveNatTransHomotopy_app (η : F ⟶ G) (n : SimplexCategoryᵒᵖ)
    (a : (nerve C).obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (F1B.kanNerveNatTransHomotopy η).h.app n (a, t) =
      ((stdSimplex.objEquiv t).toOrderHom.monotone.functor.prod' a) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁ η) := by
  let T := (nerve (C ⥤ D)).map (stdSimplex.objEquiv t).op (ComposableArrows.mk₁ η)
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (F1B.kanNerveFunctorCategoryIso_uncurry C D) n) (a.prod' T)
  change (((F1B.kanNerveFunctorCategoryIso C D).hom.app n T).app n (𝟙 n)) a = _ at h
  dsimp only [T] at h
  rw [(F1B.kanNerveFunctorCategoryIso C D).hom.naturality_apply
    (stdSimplex.objEquiv t).op] at h
  change (((F1B.kanNerveFunctorCategoryIso C D).hom.app (op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app n ((stdSimplex.objEquiv t).op ≫ 𝟙 n)) a = _ at h
  rw [Category.comp_id] at h
  change (((F1B.kanNerveFunctorCategoryIso C D).hom.app (op ⦋1⦌)
    (ComposableArrows.mk₁ η)).app n (stdSimplex.objEquiv t).op) a = _
  refine h.trans ?_
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ((ComposableArrows.mk₁ η).map
    ((stdSimplex.objEquiv t).toOrderHom.monotone.functor.map f)).naturality (a.map f)
end SerrePositivity.EInfinity.FrameHom
