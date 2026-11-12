module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import Mathlib.Tactic.FinCases

/-!
# 元の nerve ホモトピーと前後合成

概要：同じ区間関手と全単体を保持した前後合成の厳密な整合を示す。
方針：区間の二対象と元の射列の写像を照合する。
規約：自然変換の端点関手の表示変更も元の成分で比較する。
使われ方：相対自然変換のホモトピーを全語に整合させる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F G : C ⥤ D} (α : F ⟶ G)

lemma interval_congr {F' G' : C ⥤ D} (β : F' ⟶ G') (hF : F = F') (hG : G = G')
    (hα : ∀ X, HEq (α.app X) (β.app X)) :
    NerveHomotopy.interval α = NerveHomotopy.interval β := by
  subst F'
  subst G'
  have h : α = β := by
    apply NatTrans.ext
    funext X
    exact eq_of_heq (hα X)
  cases h
  rfl

lemma hom_congr {F' G' : C ⥤ D} (β : F' ⟶ G') (hF : F = F') (hG : G = G')
    (hα : ∀ X, HEq (α.app X) (β.app X)) :
    NerveHomotopy.hom α = NerveHomotopy.hom β := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun K =>
    ((SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor.prod' p.1) ⋙ K)
      (interval_congr α β hF hG hα)

lemma interval_whiskerLeft (H : E ⥤ C) :
    NerveHomotopy.interval (Functor.whiskerLeft H α) =
      (𝟭 (Fin 2)).prod H ⋙ NerveHomotopy.interval α := by
  refine CategoryTheory.Functor.ext (F := _) (G := _)
    (fun ⟨i, X⟩ => by fin_cases i <;> rfl) ?_
  rintro ⟨i, X⟩ ⟨j, Y⟩ ⟨h, f⟩
  have hij := leOfHom h
  fin_cases i <;> fin_cases j
  · change 𝟙 _ ≫ F.map (H.map f) =
      eqToHom _ ≫ (𝟙 _ ≫ F.map (H.map f)) ≫ eqToHom _
    simp
  · change α.app (H.obj X) ≫ G.map (H.map f) =
      eqToHom _ ≫ (α.app (H.obj X) ≫ G.map (H.map f)) ≫ eqToHom _
    simp
  · change (1 : Fin 2) ≤ 0 at hij
    exact (by decide : ¬ (1 : Fin 2) ≤ 0) hij |>.elim
  · change 𝟙 _ ≫ G.map (H.map f) =
      eqToHom _ ≫ (𝟙 _ ≫ G.map (H.map f)) ≫ eqToHom _
    simp

lemma interval_whiskerRight (H : D ⥤ E) :
    NerveHomotopy.interval (Functor.whiskerRight α H) = NerveHomotopy.interval α ⋙ H := by
  refine CategoryTheory.Functor.ext (F := _) (G := _)
    (fun ⟨i, X⟩ => by fin_cases i <;> rfl) ?_
  rintro ⟨i, X⟩ ⟨j, Y⟩ ⟨h, f⟩
  have hij := leOfHom h
  fin_cases i <;> fin_cases j
  · change 𝟙 _ ≫ H.map (F.map f) = eqToHom _ ≫ H.map (𝟙 _ ≫ F.map f) ≫ eqToHom _
    simp
  · change H.map (α.app X) ≫ H.map (G.map f) =
      eqToHom _ ≫ H.map (α.app X ≫ G.map f) ≫ eqToHom _
    simp
  · change (1 : Fin 2) ≤ 0 at hij
    exact (by decide : ¬ (1 : Fin 2) ≤ 0) hij |>.elim
  · change 𝟙 _ ≫ H.map (G.map f) = eqToHom _ ≫ H.map (𝟙 _ ≫ G.map f) ≫ eqToHom _
    simp

lemma hom_whiskerLeft (H : E ⥤ C) :
    NerveHomotopy.hom (Functor.whiskerLeft H α) = (nerveMap H ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫ NerveHomotopy.hom α := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change _ ⋙ NerveHomotopy.interval (Functor.whiskerLeft H α) = _
  rw [interval_whiskerLeft]
  rfl

lemma hom_whiskerRight (H : D ⥤ E) :
    NerveHomotopy.hom (Functor.whiskerRight α H) = NerveHomotopy.hom α ≫ nerveMap H := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change _ ⋙ NerveHomotopy.interval (Functor.whiskerRight α H) = _
  rw [interval_whiskerRight]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
