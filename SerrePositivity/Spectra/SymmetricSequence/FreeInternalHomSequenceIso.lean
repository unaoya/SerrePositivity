module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomAction

/-! # 自由原変数の内部Homと次数をずらした内部Homの対称列としての比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]

/-- 各段の比較を対称列全体の同型へまとめる。 -/
def freeInternalHomSequenceIso (n : ℕ) (X : C) (F : SymmetricSequence C) :
    (ihom ((freeAt n).obj X)).obj F ≅ shiftedInternalHom n X F :=
  NatIso.ofComponents (fun a => by
    cases a with | mk a => cases a with | up m => exact freeInternalHomLevelIso n m X F)
    (by
      intro a b f
      cases a with | mk a => cases a with | up m =>
        cases b with | mk b => cases b with | up k =>
          have h := FiniteBijection.card_eq_of_hom f
          change m = k at h
          subst k
          have hf : f = FiniteBijection.permutation m (FiniteBijection.equivOfHom f) := by
            exact ((FiniteBijection.homEquiv _ _).left_inv f).symm
          rw [hf]
          exact freeInternalHomLevelIso_permutation n m X F _)

/-- 対称列としての比較の第m成分は既存の各段の比較。 -/
lemma freeInternalHomSequenceIso_hom_app (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    (freeInternalHomSequenceIso n X F).hom.app (FiniteBijection.of m) =
      (freeInternalHomLevelIso n m X F).hom := rfl

/-- 対称列としての逆比較の第m成分は既存の各段の逆比較。 -/
lemma freeInternalHomSequenceIso_inv_app (n m : ℕ) (X : C) (F : SymmetricSequence C) :
    (freeInternalHomSequenceIso n X F).inv.app (FiniteBijection.of m) =
      (freeInternalHomLevelIso n m X F).inv := rfl

end SerrePositivity.SymmetricSequence
