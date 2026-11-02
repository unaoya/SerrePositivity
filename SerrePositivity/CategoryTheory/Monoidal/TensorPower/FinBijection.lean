module

public import SerrePositivity.CategoryTheory.Limits
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic

/-!
# Monoidal.TensorPower.FinBijection

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.TensorPower.FinBijection` を直接 import する。
-/

/-! ## PowerBijectionFunctor（旧 SerrePositivity/CategoryTheory/Monoidal/PowerBijectionFunctor.lean） -/

/-!
# 有限全単射圏上の反復テンソル関手

全次数の置換作用を、小さい有限全単射圏上の一つの関手にまとめる。
一般の対称モノイダル圏の構成であり、スペクトルや円には依存しない。
-/

@[expose] public section PowerBijectionFunctor
universe v u

noncomputable section

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 有限集合の濃度を反復テンソルへ、全単射を置換作用へ送る関手。 -/
def bijectionFunctor (X : C) : FiniteBijection ⥤ C :=
  FiniteBijection.familyFunctor (power X) (permutationAction X)

/-- 標準のn元集合での値は第n段の反復テンソル。 -/
lemma bijectionFunctor_obj_of (X : C) (n : ℕ) :
    (bijectionFunctor X).obj (FiniteBijection.of n) = power X n := rfl

/-- 標準の置換での値は構成した置換作用。 -/
lemma bijectionFunctor_map_permutation (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (bijectionFunctor X).map (FiniteBijection.permutation n σ) =
      (permutationAction X n σ).asIso.hom :=
  FiniteBijection.familyFunctor_map_permutation (power X) (permutationAction X) n σ

end SerrePositivity.TensorPowers
end

end PowerBijectionFunctor

/-! ## PowerBijectionAppend（旧 SerrePositivity/CategoryTheory/Monoidal/PowerBijectionAppend.lean） -/

/-! # 有限全単射圏上の反復テンソルの連結

各次数の連結同型を一つの自然変換へまとめる。
自然性は、骨格の対象の等式とブロック置換の同変性へ帰着する。
-/

@[expose] public section PowerBijectionAppend
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
end

end PowerBijectionAppend
