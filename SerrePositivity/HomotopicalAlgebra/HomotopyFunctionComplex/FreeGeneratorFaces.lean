module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorCategories
public import Mathlib.Data.Fin.Rev
public import Lean.Elab.Tactic.Omega

/-!
# 自由生成元の面の値が退化像の重なりでも一致する

## 概要
自由生成元の面の値が退化像の重なりでも一致する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0094][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0094
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual all-degree faces on the fixed-object generator presentation

These faces compare with the already constructed comonad operators. Both
ordinary and reversed face-overlap identities are strict functor equalities.
The reversed convention matches the parameter faces in the choice diagrams.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorFaces
open FreeGeneratorCategories
variable (C : Type u) [Category.{v} C]

def faceHom : (n : ℕ) → Fin (n + 1) → (degree C (n + 1) ⟶ degree C n)
  | 0, _ => FreePathResolution.comonad.ε.app (degree C 0)
  | n + 1, i => Fin.cases (FreePathResolution.comonad.ε.app (degree C (n + 1)))
      (fun j => FreePathResolution.comonad.map (faceHom n j)) i

def faceFunctor (n : ℕ) (i : Fin (n + 1)) : degree C (n + 1) ⥤ degree C n :=
  (faceHom C n i).toFunctor

lemma faceHom_zero (n : ℕ) :
    faceHom C n 0 = FreePathResolution.comonad.ε.app (degree C n) := by cases n <;> rfl

lemma faceHom_succ (n : ℕ) (i : Fin (n + 1)) :
    faceHom C (n + 1) i.succ = FreePathResolution.comonad.map (faceHom C n i) := rfl

lemma faceFunctor_obj (n : ℕ) (i : Fin (n + 1)) (X : C) : (faceFunctor C n i).obj X = X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i

lemma face_comparison_zero (n : ℕ) :
    faceHom C n 0 ≫ eqToHom (degree_power C n) =
      eqToHom (degree_power C (n + 1)) ≫
        ComonadResolutionOperators.face FreePathResolution.comonad
          (FreePathResolutionPresentation.base C) n 0 := by
  rw [faceHom_zero, degree_cast_succ, ComonadResolutionOperators.face_zero]
  exact (FreePathResolution.comonad.ε.naturality (eqToHom (degree_power C n))).symm

lemma face_comparison (n : ℕ) (i : Fin (n + 1)) :
    faceHom C n i ≫ eqToHom (degree_power C n) =
      eqToHom (degree_power C (n + 1)) ≫
        ComonadResolutionOperators.face FreePathResolution.comonad
          (FreePathResolutionPresentation.base C) n i := by
  induction n with
  | zero => fin_cases i; exact face_comparison_zero C 0
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact face_comparison_zero C (n + 1)
    | succ i =>
      rw [faceHom_succ, degree_cast_succ C n,
        ComonadResolutionOperators.face_succ]
      conv_rhs => rw [degree_cast_succ C (n + 1)]
      rw [← FreePathResolution.comonad.map_comp, ← FreePathResolution.comonad.map_comp, ih i]

lemma face_face (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    faceHom C (n + 1) j.succ ≫ faceHom C n i =
      faceHom C (n + 1) i.castSucc ≫ faceHom C n j := by
  apply (cancel_mono (eqToHom (degree_power C n))).1
  have transport (a : Fin (n + 2)) (b : Fin (n + 1)) :
      (faceHom C (n + 1) a ≫ faceHom C n b) ≫ eqToHom (degree_power C n) =
        eqToHom (degree_power C (n + 2)) ≫
          (ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 1) a ≫
          ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) n b) := by
    rw [Category.assoc, face_comparison, ← Category.assoc, face_comparison, Category.assoc]
  rw [transport, transport, ComonadResolutionOperators.face_face _ _ n i j h]

lemma faceFunctor_faceFunctor (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    faceFunctor C (n + 1) j.succ ⋙ faceFunctor C n i =
      faceFunctor C (n + 1) i.castSucc ⋙ faceFunctor C n j :=
  congrArg Cat.Hom.toFunctor (face_face C n i j h)

lemma faceFunctor_overlap (n : ℕ) (i j : Fin (n + 2)) (h : i < j) :
    faceFunctor C (n + 1) j ⋙ faceFunctor C n (i.castPred (Fin.ne_last_of_lt h)) =
      faceFunctor C (n + 1) i ⋙ faceFunctor C n (j.pred (Fin.ne_zero_of_lt h)) := by
  let a := i.castPred (Fin.ne_last_of_lt h)
  let b := j.pred (Fin.ne_zero_of_lt h)
  have hab : a ≤ b := by
    change i.val ≤ j.val - 1
    omega
  simpa only [a, b, Fin.castSucc_castPred, Fin.succ_pred] using
    faceFunctor_faceFunctor C n a b hab

def reverseFace (n : ℕ) (i : Fin (n + 1)) : degree C (n + 1) ⥤ degree C n :=
  faceFunctor C n i.rev

lemma reverseFace_obj (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (reverseFace C n i).obj X = X := faceFunctor_obj C n i.rev X

lemma reverseFace_overlap (n : ℕ) (j k : Fin (n + 2)) (hjk : j < k) :
    reverseFace C (n + 1) j ⋙ reverseFace C n (k.pred (Fin.ne_zero_of_lt hjk)) =
      reverseFace C (n + 1) k ⋙ reverseFace C n (j.castPred (Fin.ne_last_of_lt hjk)) := by
  have hrev : k.rev < j.rev := Fin.rev_lt_rev.mpr hjk
  unfold reverseFace
  rw [Fin.rev_pred, Fin.rev_castPred]
  exact faceFunctor_overlap C n k.rev j.rev hrev

/-- The same reversed face, with its object function definitionally the identity. -/
def fixedFace (n : ℕ) (i : Fin (n + 1)) : degree C (n + 1) ⥤ degree C n where
  obj X := X
  map {X Y} f := eqToHom (reverseFace_obj C n i X).symm ≫
    (reverseFace C n i).map f ≫ eqToHom (reverseFace_obj C n i Y)
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

lemma fixedFace_eq (n : ℕ) (i : Fin (n + 1)) : fixedFace C n i = reverseFace C n i := by
  refine CategoryTheory.Functor.ext (fun X => (reverseFace_obj C n i X).symm) ?_
  intro X Y f
  simp [fixedFace]

/-- 自由生成元の面の値が退化像の重なりでも一致する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
lemma fixedFace_overlap (n : ℕ) (j k : Fin (n + 2)) (hjk : j < k) :
    fixedFace C (n + 1) j ⋙ fixedFace C n (k.pred (Fin.ne_zero_of_lt hjk)) =
      fixedFace C (n + 1) k ⋙ fixedFace C n (j.castPred (Fin.ne_last_of_lt hjk)) := by
  simp only [fixedFace_eq]
  exact reverseFace_overlap C n j k hjk

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorFaces
