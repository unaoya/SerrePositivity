module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero

/-!
# 二入力演算の先頭への零入力の代入

概要：BF §1・BM §1 の nullary 代入を二項積の左単位の図式へ移す。
方針：先頭代入の公式を使い、単位子の自然性と整合性で正規化する。
規約：実際の単位因子と右括弧の反復冪を使う。
使われ方：E 代数の H⁰ の積の単位則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.HomologyZero

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：先頭への零入力代入は元の左入力へ単位を入れる射（BF §1、BM §1）。
方針：先頭代入の公式の arity を計算し、単位子の整合性を使う。
規約：零入力射は任意、単位則はまだ仮定しない。
使われ方：E の部分合成のホモトピーを二項積の単位則へ移す。 -/
lemma nullaryBinaryInsertion (X : Complex A) (η : 𝟙_ (Complex A) ⟶ X) :
    (oneIso X).inv ≫ (λ_ (power X 1)).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X (𝟙_ (Complex A)) 1 0 0 ((λ_ (𝟙_ (Complex A))).hom ≫ η) =
    (λ_ X).inv ≫ (η ▷ X) ≫ (X ◁ (oneIso X).inv) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]
  simp only [appendIso, Iso.trans_inv, eqToIso.inv, oneIso, power, eqToHom_refl,
    whiskerLeft_id, Category.id_comp, comp_whiskerRight]
  monoidal

end SerrePositivity.HomologyZero
