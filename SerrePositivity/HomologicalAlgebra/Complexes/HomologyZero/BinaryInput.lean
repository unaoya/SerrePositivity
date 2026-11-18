module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation

/-!
# 二入力のテンソルと反復冪の交換の比較

概要：BF §1 の二入力の等変性を通常の二因子テンソルの交換へ移す。
方針：二乗に残る単位因子の挿入と隣接交換の整合性を証明する。
規約：一般の対称モノイダル圏、既存の右に括った反復冪。
使われ方：E 代数の H⁰ の積の可換性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.TensorPowers

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：二因子の交換は二乗テンソル冪の隣接交換と一致（BF §1）。
方針：隣接交換の定義を展開し、右単位子のテンソル則と自然性を使う。
規約：単位因子の挿入を両辺で明示する。
使われ方：代数の対称群等変性を二項積の可換性へ移す。 -/
lemma binaryInput_braiding (X : C) :
    (β_ X X).hom ≫ (X ◁ (oneIso X).inv) =
      (X ◁ (oneIso X).inv) ≫
        (permutationAction X 2 (_root_.SerrePositivity.Coxeter.adjacentTransposition (0 : Fin 1))).asIso.hom := by
  rw [permutationAction_adjacent]
  change (β_ X X).hom ≫ (X ◁ (ρ_ X).inv) =
    (X ◁ (ρ_ X).inv) ≫ (swapFirstIso X 0).hom
  simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, power]
  rw [← rightUnitor_tensor_inv_assoc, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.HomologyZero
