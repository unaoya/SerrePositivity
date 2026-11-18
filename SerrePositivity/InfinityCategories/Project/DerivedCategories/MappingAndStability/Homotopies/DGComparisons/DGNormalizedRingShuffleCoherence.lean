module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.SignInversions
public import SerrePositivity.EInfinity.BarrattEccles.TripleShuffleCoordinates
public import SerrePositivity.EInfinity.BarrattEccles.TripleShufflePermutation
/-!
概要：単体環の実正規化乗法と、元の shuffle の経路・符号の整合性。
方針：既存の実 shuffle 鎖写像と同じ有限和の座標・係数を使う。
規約：元の非可換な積と全次数を保つ。使われ方：β5(g) の dg 代数化。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial
namespace NormalizedRingShuffle
open EInfinity.BarrattEccles
lemma left_eq_horizontal {p q : ℕ} (s : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left s = s.horizontalMap := rfl
lemma right_eq_vertical {p q : ℕ} (s : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right s rfl = s.verticalMap := rfl
lemma inversions_eq {p q : ℕ} (s : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions s = _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber s.val := rfl
lemma sign_eq {p q : ℕ} (s : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions s = (s.sign : ℤ) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sign_eq_pow_inversionNumber, inversions_eq]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
def associationMap (p q r : ℕ) : ⦋p + q + r⦌ ⟶ ⦋p + (q + r)⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.cast (congrArg Nat.succ (Nat.add_assoc p q r))
      monotone' := fun _ _ h ↦ h }
lemma triple_first (p q r : ℕ)
    (v : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath (p + q) r × _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left v.1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left v.2 =
      associationMap p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).1 := by
  ext k
  exact congrArg Fin.val (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffle_first_coordinate p q r v k)
lemma triple_second (p q r : ℕ)
    (v : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath (p + q) r × _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left v.1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right v.2 rfl =
      associationMap p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).1 rfl ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.left (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).2 := by
  ext k
  exact congrArg Fin.val (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffle_second_coordinate p q r v k)
lemma triple_third (p q r : ℕ)
    (v : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath (p + q) r × _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right v.1 rfl =
      associationMap p q r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).1 rfl ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.right (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).2 rfl := by
  ext k
  exact congrArg Fin.val (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffle_third_coordinate p q r v k)
lemma triple_sign (p q r : ℕ)
    (v : _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath (p + q) r × _root_.SerrePositivity.EInfinity.BarrattEccles.ShufflePath p q) :
    (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions v.1 * (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions v.2 =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).1 *
        (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleIndex.inversions (_root_.SerrePositivity.EInfinity.BarrattEccles.tripleShuffleEquiv p q r v).2 := by
  simp_rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.sign_eq]
  exact congrArg Units.val (tripleShuffle_sign p q r v)
end NormalizedRingShuffle
end SerrePositivity.InfinityCategories.Project.DerivedCategories
