module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorFaces

/-!
# 中断した任意モデル源への一般化：FreeGeneratorMixedOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All mixed face-degeneracy equations on the actual fixed-object resolution。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0096][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0096
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All mixed face-degeneracy equations on the actual fixed-object resolution

The equations are transported from the existing comonad resolution using its
proved comparison squares. Raw face indices are convenient for comparing
with simplex identities before reversing the parameter indices.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorMixedOperators
open FreeGeneratorCategories FreeGeneratorFaces
variable (C : Type u) [Category.{v} C]

/-- A face with ordinary source indexing and a definitionally fixed object function. -/
def rawFace (n : ℕ) (i : Fin (n + 1)) : degree C (n + 1) ⥤ degree C n :=
  fixedFace C n i.rev

lemma rawFace_eq (n : ℕ) (i : Fin (n + 1)) : rawFace C n i = faceFunctor C n i := by
  simp only [rawFace, fixedFace_eq, reverseFace, Fin.rev_rev]

lemma degeneracy_face_self (n : ℕ) (i : Fin (n + 1)) :
    degeneracyFunctor C n i ⋙ rawFace C (n + 1) i.castSucc = 𝟭 _ := by
  have hh : (degeneracyFunctor C n i).toCatHom ≫ faceHom C (n + 1) i.castSucc = 𝟙 _ := by
    apply (cancel_mono (eqToHom (degree_power C (n + 1)))).1
    rw [Category.assoc, face_comparison, ← Category.assoc, degeneracy_comparison,
      Category.assoc, ComonadResolutionOperators.degeneracy_face_self,
      Category.comp_id, Category.id_comp]
  rw [rawFace_eq]
  exact congrArg Cat.Hom.toFunctor hh

lemma degeneracy_face_succ (n : ℕ) (i : Fin (n + 1)) :
    degeneracyFunctor C n i ⋙ rawFace C (n + 1) i.succ = 𝟭 _ := by
  have hh : (degeneracyFunctor C n i).toCatHom ≫ faceHom C (n + 1) i.succ = 𝟙 _ := by
    apply (cancel_mono (eqToHom (degree_power C (n + 1)))).1
    rw [Category.assoc, face_comparison, ← Category.assoc, degeneracy_comparison,
      Category.assoc, ComonadResolutionOperators.degeneracy_face_succ,
      Category.comp_id, Category.id_comp]
  rw [rawFace_eq]
  exact congrArg Cat.Hom.toFunctor hh

lemma degeneracy_face_le (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) :
    degeneracyFunctor C (n + 1) j.succ ⋙ rawFace C (n + 2) i.castSucc =
      rawFace C (n + 1) i ⋙ degeneracyFunctor C n j := by
  have hh : (degeneracyFunctor C (n + 1) j.succ).toCatHom ≫ faceHom C (n + 2) i.castSucc =
      faceHom C (n + 1) i ≫ (degeneracyFunctor C n j).toCatHom := by
    apply (cancel_mono (eqToHom (degree_power C (n + 2)))).1
    calc
      _ = eqToHom (degree_power C (n + 2)) ≫
          (ComonadResolutionOperators.degeneracy FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 1) j.succ ≫
          ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 2) i.castSucc) := by
        rw [Category.assoc, face_comparison, ← Category.assoc, degeneracy_comparison,
          Category.assoc]
      _ = eqToHom (degree_power C (n + 2)) ≫
          (ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 1) i ≫
          ComonadResolutionOperators.degeneracy FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) n j) := by
        rw [ComonadResolutionOperators.degeneracy_face_le _ _ n i j h]
      _ = _ := by
        symm
        rw [Category.assoc, degeneracy_comparison, ← Category.assoc, face_comparison,
          Category.assoc]
  simp only [rawFace_eq]
  exact congrArg Cat.Hom.toFunctor hh

lemma degeneracy_face_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) :
    degeneracyFunctor C (n + 1) j.castSucc ⋙ rawFace C (n + 2) i.succ =
      rawFace C (n + 1) i ⋙ degeneracyFunctor C n j := by
  have hh : (degeneracyFunctor C (n + 1) j.castSucc).toCatHom ≫ faceHom C (n + 2) i.succ =
      faceHom C (n + 1) i ≫ (degeneracyFunctor C n j).toCatHom := by
    apply (cancel_mono (eqToHom (degree_power C (n + 2)))).1
    calc
      _ = eqToHom (degree_power C (n + 2)) ≫
          (ComonadResolutionOperators.degeneracy FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 1) j.castSucc ≫
          ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 2) i.succ) := by
        rw [Category.assoc, face_comparison, ← Category.assoc, degeneracy_comparison,
          Category.assoc]
      _ = eqToHom (degree_power C (n + 2)) ≫
          (ComonadResolutionOperators.face FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) (n + 1) i ≫
          ComonadResolutionOperators.degeneracy FreePathResolution.comonad
            (FreePathResolutionPresentation.base C) n j) := by
        rw [ComonadResolutionOperators.degeneracy_face_gt _ _ n i j h]
      _ = _ := by
        symm
        rw [Category.assoc, degeneracy_comparison, ← Category.assoc, face_comparison,
          Category.assoc]
  simp only [rawFace_eq]
  exact congrArg Cat.Hom.toFunctor hh

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorMixedOperators
