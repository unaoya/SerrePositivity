module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
模型。文献の定義との比較は後で
# 底の同型からのオペラッド代数の同型

概要：Berger–Moerdijk §1 の代数の作用を保つ底の同型を代数の同型にする。
方針：逆射の作用保存を元の同型で後合成して検証する。
規約：任意のオペラッドと全入力数を扱う。
使われ方：単位余代数からの convolution と元の代数の比較同型を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：作用を保つ底の複体の同型から代数の同型を得る（BM §1）。
方針：逆射の保存則を元の射で後合成し、テンソル冪の合成保存で相殺する。
規約：作用保存は順方向だけを入力に取る。
使われ方：標準の Hom の単位同型をオペラッド代数へ上げる。 -/
def isoOfCarrierIso {X Y : P.Algebra} (e : X.carrier ≅ Y.carrier)
    (h : ∀ n : ℕ, X.action n ≫ e.hom =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map e.hom n) ≫ Y.action n) : X ≅ Y where
  hom := { hom := e.hom, comm := h }
  inv := {
    hom := e.inv
    comm n := by
      apply (cancel_mono e.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [h, tensorHom_comp_tensorHom_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp]
      simp only [Iso.inv_hom_id, _root_.SerrePositivity.TensorPowers.map_id, Category.id_comp,
        tensorHom_id, id_whiskerRight] }
  hom_inv_id := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext e.hom_inv_id
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext e.inv_hom_id

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra
