module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # 左の tensor 作用を右作用へ移す三因子交換
概要：ラベル・前入力・後入力の順を、元の二回作用が使う逆順へ移す交換射を比較する。
方針：元の braiding の自然性・Yang–Baxter 等号と対称性を使う。
規約：対称性は dg tensor の基底にのみ使う。使われ方：実 Perf 右作用の結合則。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory BraidedCategory
variable {C : Type u} [Category C] [MonoidalCategory C]

section Braided
variable [BraidedCategory C]

/-- 三因子を元の後入力・前入力・ラベルの順へ移す交換射。 -/
def rightActionReverse (X F G : C) : (X ⊗ F) ⊗ G ⟶ (G ⊗ F) ⊗ X :=
  (β_ (X ⊗ F) G).hom ≫ (𝟙 G ⊗ₘ (β_ X F).hom) ≫ (α_ G F X).inv

/-- 元の三因子交換は、同じ全反転を別の二つの交換で表した射に等しい。 -/
lemma rightActionReverse_eq (X F G : C) :
    rightActionReverse X F G =
      (α_ X F G).hom ≫ (β_ X (F ⊗ G)).hom ≫ ((β_ F G).hom ⊗ₘ 𝟙 X) := by
  apply (cancel_epi (α_ X F G).inv).mp
  apply (cancel_mono (α_ G F X).hom).mp
  simp only [rightActionReverse, id_tensorHom, tensorHom_id, braiding_tensor_left_hom,
    braiding_tensor_right_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact (yang_baxter X F G).symm

/-- 二回の右作用の元の射は、全反転の後の同じ二回の左作用に等しい。 -/
lemma rightActionReverse_iteration {X F G Y Z : C} (f : F ⊗ X ⟶ Y) (g : G ⊗ Y ⟶ Z) :
    (((β_ X F).hom ≫ f) ⊗ₘ 𝟙 G) ≫ (β_ Y G).hom ≫ g =
      rightActionReverse X F G ≫ (α_ G F X).hom ≫ (𝟙 G ⊗ₘ f) ≫ g := by
  rw [braiding_naturality_assoc]
  simp only [rightActionReverse, Category.assoc, Iso.inv_hom_id_assoc,
    tensorHom_comp_tensorHom_assoc, Category.id_comp]

end Braided

section Symmetric
variable [SymmetricCategory C]

/-- 元の全反転の後に入力二因子を戻すと、ラベルと入力の組の同じ交換になる。 -/
lemma rightActionReverse_rotate (X F G : C) :
    rightActionReverse X F G ≫ ((β_ G F).hom ⊗ₘ 𝟙 X) =
      (α_ X F G).hom ≫ (β_ X (F ⊗ G)).hom := by
  rw [rightActionReverse_eq]
  simp only [tensorHom_id, Category.assoc, ← comp_whiskerRight, SymmetricCategory.symmetry,
    id_whiskerRight, Category.comp_id]

/-- 元の左作用の同じ三因子等号は、signed 交換を保持した右作用の結合等号を与える。 -/
lemma rightActionPairing_associativity {X F G Y Z U W : C}
    (f : F ⊗ X ⟶ Y) (g : G ⊗ Y ⟶ Z) (c : Z ⟶ W)
    (h : F ⊗ G ⟶ U) (k : U ⊗ X ⟶ W)
    (hc : ((α_ G F X).hom ≫ (𝟙 G ⊗ₘ f) ≫ g) ≫ c =
      (((β_ G F).hom ≫ h) ⊗ₘ 𝟙 X) ≫ k) :
    ((((β_ X F).hom ≫ f) ⊗ₘ 𝟙 G) ≫ (β_ Y G).hom ≫ g) ≫ c =
      (α_ X F G).hom ≫ (𝟙 X ⊗ₘ h) ≫ (β_ X U).hom ≫ k := by
  have ht : (((β_ G F).hom ≫ h) ⊗ₘ 𝟙 X) =
      ((β_ G F).hom ⊗ₘ 𝟙 X) ≫ (h ⊗ₘ 𝟙 X) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  calc
    _ = rightActionReverse X F G ≫ (((α_ G F X).hom ≫ (𝟙 G ⊗ₘ f) ≫ g) ≫ c) := by
      rw [rightActionReverse_iteration]
      simp only [Category.assoc]
    _ = rightActionReverse X F G ≫ ((((β_ G F).hom ≫ h) ⊗ₘ 𝟙 X) ≫ k) :=
      congrArg (fun q => rightActionReverse X F G ≫ q) hc
    _ = (rightActionReverse X F G ≫ ((β_ G F).hom ⊗ₘ 𝟙 X)) ≫ (h ⊗ₘ 𝟙 X) ≫ k := by
      rw [ht]
      simp only [Category.assoc]
    _ = (α_ X F G).hom ≫ (β_ X (F ⊗ G)).hom ≫ (h ⊗ₘ 𝟙 X) ≫ k := by
      rw [rightActionReverse_rotate]
      simp only [Category.assoc]
    _ = _ := by rw [← braiding_naturality_assoc]

end Symmetric

end SerrePositivity.KST.SConstruction
