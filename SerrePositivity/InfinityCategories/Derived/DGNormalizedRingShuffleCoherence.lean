module
public import SerrePositivity.KST.ProExcision.ShuffleIndex
public import SerrePositivity.EInfinity.Shuffle.SignInversions
public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.TripleShufflePermutation
/-!
概要：単体環の実正規化乗法と、元の shuffle の経路・符号の整合性。
方針：既存の実 shuffle 鎖写像と同じ有限和の座標・係数を使う。
規約：元の非可換な積と全次数を保つ。使われ方：β5(g) の dg 代数化。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories
open CategoryTheory
open scoped Simplicial
namespace NormalizedRingShuffle
open KST.ProExcision EInfinity.BarrattEccles
lemma left_eq_horizontal {p q : ℕ} (s : ShufflePath p q) :
    ShuffleIndex.left s = s.horizontalMap := rfl
lemma right_eq_vertical {p q : ℕ} (s : ShufflePath p q) :
    ShuffleIndex.right s rfl = s.verticalMap := rfl
lemma inversions_eq {p q : ℕ} (s : ShufflePath p q) :
    ShuffleIndex.inversions s = EInfinity.Shuffle.inversionNumber s.val := rfl
lemma sign_eq {p q : ℕ} (s : ShufflePath p q) :
    (-1 : ℤ) ^ ShuffleIndex.inversions s = (s.sign : ℤ) := by
  rw [EInfinity.Shuffle.sign_eq_pow_inversionNumber, inversions_eq]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
def associationMap (p q r : ℕ) : ⦋p + q + r⦌ ⟶ ⦋p + (q + r)⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.cast (congrArg Nat.succ (Nat.add_assoc p q r))
      monotone' := fun _ _ h ↦ h }
lemma triple_first (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    ShuffleIndex.left v.1 ≫ ShuffleIndex.left v.2 =
      associationMap p q r ≫ ShuffleIndex.left (tripleShuffleEquiv p q r v).1 := by
  ext k
  exact congrArg Fin.val (tripleShuffle_first_coordinate p q r v k)
lemma triple_second (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    ShuffleIndex.left v.1 ≫ ShuffleIndex.right v.2 rfl =
      associationMap p q r ≫ ShuffleIndex.right (tripleShuffleEquiv p q r v).1 rfl ≫
        ShuffleIndex.left (tripleShuffleEquiv p q r v).2 := by
  ext k
  exact congrArg Fin.val (tripleShuffle_second_coordinate p q r v k)
lemma triple_third (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    ShuffleIndex.right v.1 rfl =
      associationMap p q r ≫ ShuffleIndex.right (tripleShuffleEquiv p q r v).1 rfl ≫
        ShuffleIndex.right (tripleShuffleEquiv p q r v).2 rfl := by
  ext k
  exact congrArg Fin.val (tripleShuffle_third_coordinate p q r v k)
lemma triple_sign (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    (-1 : ℤ) ^ ShuffleIndex.inversions v.1 * (-1 : ℤ) ^ ShuffleIndex.inversions v.2 =
      (-1 : ℤ) ^ ShuffleIndex.inversions (tripleShuffleEquiv p q r v).1 *
        (-1 : ℤ) ^ ShuffleIndex.inversions (tripleShuffleEquiv p q r v).2 := by
  simp_rw [sign_eq]
  exact congrArg Units.val (tripleShuffle_sign p q r v)
end NormalizedRingShuffle
end SerrePositivity.InfinityCategories
