module

public import SerrePositivity.CategoryTheory.Monoidal.PowerBijectionFunctor
public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockPermutations
public import SerrePositivity.CategoryTheory.FiniteBijectionSum
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic

/-! # 有限全単射圏上の反復テンソルの連結

各次数の連結同型を一つの自然変換へまとめる。
自然性は、骨格の対象の等式とブロック置換の同変性へ帰着する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory SerrePositivity.FiniteBijection

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 二つの反復テンソルを直和次数へ連結する自然変換。 -/
def appendNatTrans (X : C) :
    externalProduct (bijectionFunctor X) (bijectionFunctor X) ⟶
      sumFunctor ⋙ bijectionFunctor X where
  app A := (appendIso X (card A.1) (card A.2)).hom
  naturality := by
    rintro ⟨A, B⟩ ⟨A', B'⟩ ⟨f, g⟩
    cases object_eq_of_hom f
    cases object_eq_of_hom g
    simpa only [externalProductBifunctor_obj_map, Functor.comp_map, bijectionFunctor, familyFunctor,
      familyMap, finCongr_refl, Equiv.trans_refl, eqToHom_refl, Category.comp_id,
      sumFunctor, sumMap, equivOfHom_homOfEquiv, sumObj, card_of, tensorHom_def] using
      appendIso_block_permutation X (card A) (card B) (equivOfHom f) (equivOfHom g)

/-- 連結の成分は既存の次数の連結同型。 -/
lemma appendNatTrans_app (X : C) (A B : FiniteBijection) :
    (appendNatTrans X).app (A, B) = (appendIso X (card A) (card B)).hom := rfl

end SerrePositivity.TensorPowers
