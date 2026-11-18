module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorStandardInclusion
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientProjections
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks

/-!
# 標準二色入力の分離とブロック置換

HA 3.2.4.7 の自由比較のため、指定された標準入力の同型が
両ブロックの実際の signed permutation action と可換であることを示す。
包含の式とその左逆で照合し、任意の複体の微分を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 左右の冪を指定した二色順序で和の冪へ含める。 -/
def binaryTensorStandardPowersInclusion (m n : ℕ) :
    power X m ⊗ power Y n ⟶ power (X ⊞ Y) (m + n) :=
  (TensorPowers.map (biprod.inl : X ⟶ X ⊞ Y) m ⊗ₘ
    TensorPowers.map (biprod.inr : Y ⟶ X ⊞ Y) n) ≫ (appendIso (X ⊞ Y) m n).hom

/-- 指定連結包含は、両ブロックの実際の置換作用と可換。 -/
lemma binaryTensorStandardPowersInclusion_block (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    ((permutationAction X m σ).asIso.hom ⊗ₘ (permutationAction Y n τ).asIso.hom) ≫
      binaryTensorStandardPowersInclusion X Y m n =
    binaryTensorStandardPowersInclusion X Y m n ≫
      (permutationAction (X ⊞ Y) (m + n) (FiniteBijection.blockEquiv σ τ)).asIso.hom := by
  unfold binaryTensorStandardPowersInclusion
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality A (biprod.inl : X ⟶ X ⊞ Y) m σ,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_permutation_naturality A (biprod.inr : Y ⟶ X ⊞ Y) n τ,
    ← tensorHom_comp_tensorHom, Category.assoc, appendIso_block_permutation]
  exact (Category.assoc _ _ _).symm

/-- 標準入力の分離同型の逆射の後の包含は、左右の冪の指定連結包含。 -/
lemma binaryTensorStandardPowersIso_inv_inclusion (m n : ℕ) :
    (binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) =
        binaryTensorStandardPowersInclusion X Y m n := by
  rw [binaryTensorStandardPowersIso_inclusion]
  change (binaryTensorStandardPowersIso X Y m n).inv ≫
    (binaryTensorStandardPowersIso X Y m n).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- 標準入力の指定同型は、両ブロックの置換を冪ごとの置換へ移す。 -/
lemma binaryTensorStandardPowersIso_block (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (binaryTensorWordFixedIso X Y (m + n) (binaryTensorStandardPattern m n)
      (FiniteBijection.blockEquiv σ τ) (binaryTensorStandardPattern_block_fixed m n σ τ)).hom ≫
        (binaryTensorStandardPowersIso X Y m n).hom =
    (binaryTensorStandardPowersIso X Y m n).hom ≫
      ((permutationAction X m σ).asIso.hom ⊗ₘ (permutationAction Y n τ).asIso.hom) := by
  apply (cancel_mono (binaryTensorStandardPowersIso X Y m n).inv).1
  apply binaryTensorWordInclusion_cancel X Y (binaryTensorStandardPattern m n)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [binaryTensorStandardPowersIso_inv_inclusion,
    binaryTensorWordFixedIso_inclusion, binaryTensorStandardPowersIso_inclusion]
  change (binaryTensorStandardPowersIso X Y m n).hom ≫
      binaryTensorStandardPowersInclusion X Y m n ≫ _ =
    (binaryTensorStandardPowersIso X Y m n).hom ≫ _ ≫
      binaryTensorStandardPowersInclusion X Y m n
  rw [binaryTensorStandardPowersInclusion_block]

private lemma binaryTensorFixedIso_perm_eq (r : ℕ) (w : BinaryTensorWord r)
    (σ τ : Equiv.Perm (Fin r)) (h : σ = τ) (hσ : σ • w = w) (hτ : τ • w = w) :
    binaryTensorWordFixedIso X Y r w σ hσ = binaryTensorWordFixedIso X Y r w τ hτ := by
  subst τ
  rfl

namespace BarrattEccles

/-- 実際の二色部分群の作用についての、同じ分離同型の可換式。 -/
lemma twoColorStandardPowersIso_action (m n : ℕ) (g : TwoColorGroup.{u} m n) :
    (binaryTensorWordFixedIso X Y (m + n) (binaryTensorStandardPattern m n)
      (twoColorInputPermutation m n g) (twoColorInputPermutation_fixed m n g)).hom ≫
        (binaryTensorStandardPowersIso X Y m n).hom =
    (binaryTensorStandardPowersIso X Y m n).hom ≫
      ((permutationAction X m (twoColorLeftProjection m n g).down).asIso.hom ⊗ₘ
        (permutationAction Y n (twoColorRightProjection m n g).down).asIso.hom) := by
  have hp : twoColorInputPermutation m n g =
      FiniteBijection.blockEquiv (twoColorLeftProjection m n g).down
        (twoColorRightProjection m n g).down := by
    change g.val.down = _
    exact twoColorGroup_block m n g
  have he := binaryTensorFixedIso_perm_eq X Y (m + n) (binaryTensorStandardPattern m n)
    _ _ hp (twoColorInputPermutation_fixed m n g)
    (binaryTensorStandardPattern_block_fixed m n
      (twoColorLeftProjection m n g).down (twoColorRightProjection m n g).down)
  rw [he]
  exact binaryTensorStandardPowersIso_block X Y m n
    (twoColorLeftProjection m n g).down (twoColorRightProjection m n g).down

end BarrattEccles
end SerrePositivity.EInfinity
