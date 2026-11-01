module

public import SerrePositivity.InfinityCategories.Kan.Pointed.DiscreteInternalHom
public import SerrePositivity.KST.Spectra.FreeActionEndNaturality

/-!
概要：離散内部 Hom と自由作用の end の比較同型のパラメーター付きの具体式。
方針：Hom の自然な同値を恒等射への前合成として読み戻す。
規約：通常の射の厳密な等式。
使われ方：Goerss–Jardine I §7、VIII §2。cochain の座標表示と基点の計算。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.HomotopyLimits

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma DiscreteInternalHom.iso_hom (S : Type u) (X : SSet.{u}) :
    (iso S X).hom = homEquiv S X _ (𝟙 _) := rfl

lemma DiscreteInternalHom.homEquiv_apply (S : Type u) (X : SSet.{u}) {A : SSet.{u}}
    (t : A ⟶ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj X) :
    homEquiv S X A t = t ≫ (iso S X).hom := by
  rw [iso_hom, ← homEquiv_pre, Category.comp_id]

lemma DiscreteInternalHom.comp_iso (S : Type u) (X : SSet.{u}) {A : SSet.{u}}
    (t : A ⟶ (ihom ((Functor.const (SimplexCategoryᵒᵖ)).obj S)).obj X) :
    t ≫ (iso S X).hom = toFunctions S X (uncurry t) :=
  (homEquiv_apply S X t).symm

lemma FreeActionFamily.comp_endIso {G : Type u} [Group G] (S : Type u) (B : Action SSet.{u} G)
    {A : SSet.{u}} (t : A ⟶ weightedSections (weight S) (coefficients B)) :
    t ≫ (endIso S B).hom = homEquiv S B A t := by
  rw [endIso_hom, ← homEquiv_pre, Category.comp_id]

end

end SerrePositivity.KST.Spectra
