module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 自由表現可能前層の射影性

## 概要
射影的な係数対象から作る自由表現可能前層は、前層圏でも射影的である。

## 方針
自由 Yoneda の Hom 同値で持ち上げを一つの評価値へ戻し、係数の射影性を用いる。

## 規約
必要な余積と押し出しの存在を明記し、添字圏の加法性は要求しない。

## 使われ方
Weibel §2.2、HA 1.2.4。標準単体の線形鎖と bar 重みを射影分解として比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u v' u'
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.HomologicalAlgebra

/-- 射影係数を持つ自由表現可能前層は射影的。 -/
theorem freeYoneda_projective {J : Type u} [Category.{v} J]
    {C : Type u'} [Category.{v'} C] [HasCoproducts.{v} C] [HasPushouts C]
    (j : J) (P : C) [Projective P] : Projective (Presheaf.freeYoneda j P) where
  factors {E F} f e _ := by
    have : Epi (e.app (op j)) := inferInstance
    obtain ⟨g, hg⟩ := Projective.factors (Presheaf.freeYonedaHomEquiv f) (e.app (op j))
    refine ⟨Presheaf.freeYonedaHomEquiv.symm g, ?_⟩
    apply Presheaf.freeYonedaHomEquiv.injective
    rw [Presheaf.freeYonedaHomEquiv_comp, Equiv.apply_symm_apply, hg]

end SerrePositivity.HomologicalAlgebra
