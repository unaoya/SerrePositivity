module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordFixedCutLength
public import Mathlib.CategoryTheory.Functor.Category

/-!
# 元の長さ零の全成分を持つ自然変換の厳密な回収

概要：射列の圏値の自然変換の全成分が長さ零なら、関手の等式による元の移送に一致する。
方針：元の各成分から対象の等式を回収し、自然性から全射を照合する。
規約：自然変換全体と元の全対象・全射を保持する。
使われ方：貼り戻し後の内部接続列を恒等列の挿入へ照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {A B : D ⥤ Paths C}

lemma zeroNatTrans_eqToHom (α : A ⟶ B) (hα : ∀ d, (α.app d).length = 0) :
    ∃ h : A = B, α = eqToHom h := by
  classical
  let e (d : D) : A.obj d = B.obj d :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_eqToHom_of_length_zero (α.app d) (hα d)).choose
  have he (d : D) : α.app d = eqToHom (e d) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_eqToHom_of_length_zero (α.app d) (hα d)).choose_spec
  have hAB : A = B := by
    refine Functor.ext (F := A) (G := B) e ?_
    intro d f k
    have hn := α.naturality k
    rw [he d, he f] at hn
    have hc := congrArg (fun p => p ≫ eqToHom (e f).symm) hn
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hc
  refine ⟨hAB, ?_⟩
  apply NatTrans.ext
  funext d
  rw [eqToHom_app]
  exact he d

lemma zeroNatTrans_heq_id {K : D ⥤ Paths C} (α : A ⟶ B)
    (hα : ∀ d, (α.app d).length = 0) (hB : B = K) : HEq α (𝟙 K) := by
  obtain ⟨he, h⟩ := zeroNatTrans_eqToHom α hα
  cases hB
  cases he
  exact heq_of_eq h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
