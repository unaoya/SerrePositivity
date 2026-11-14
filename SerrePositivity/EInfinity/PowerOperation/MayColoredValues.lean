module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedCycles
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorWords

/-!
# May の反復入力の二色展開

May, Proposition 2.3(ii) の混合項を、既存の BinaryTensorWord と同じ語で表す。
同次入力の閉性を保ち、全語の和が (a+b)^{⊗n} に一致する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {k : Type u} [CommRing k]

/-- 既存の二色語に従い、同じ次数の a,b を元のテンソル冪へ入力する。 -/
def mayColoredValue (K : Complex k) (q : ℤ) (a b : K.X q) :
    (n : ℕ) → BinaryTensorWord n → (power K n).X (mayRepeatedDegree q n)
  | 0, _ => mayTensorUnitValue
  | n + 1, .inl w => ιTensorObj K (power K n) q (mayRepeatedDegree q n)
      (mayRepeatedDegree q (n + 1)) rfl (a ⊗ₜ[k] mayColoredValue K q a b n w)
  | n + 1, .inr w => ιTensorObj K (power K n) q (mayRepeatedDegree q n)
      (mayRepeatedDegree q (n + 1)) rfl (b ⊗ₜ[k] mayColoredValue K q a b n w)

/-- 二色語の全入力が閉じていれば、各語の同次テンソルも閉じる。 -/
lemma mayColoredValue_cycle (K : Complex k) (q : ℤ) (a b : K.X q)
    (ha : K.d q (q + 1) a = 0) (hb : K.d q (q + 1) b = 0)
    (n : ℕ) (w : BinaryTensorWord n) :
    (power K n).d (mayRepeatedDegree q n) (mayRepeatedDegree q n + 1)
      (mayColoredValue K q a b n w) = 0 := by
  induction n with
  | zero =>
    change (𝟙_ (Complex k)).d 0 1 mayTensorUnitValue = 0
    have hd : (𝟙_ (Complex k)).d 0 1 = 0 := rfl
    rw [hd]
    rfl
  | succ n ih =>
    cases w <;>
      change (cochainTensor K (power K n)).d _ _
        (ιTensorObj K (power K n) _ _ _ _ (_ ⊗ₜ[k] mayColoredValue K q a b n _)) = 0
    all_goals
      rw [cochainTensor_d_apply_ι, ih]
      first | rw [ha] | rw [hb]
      simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
      change (ιTensorObj K (power K n) _ _ _ _).hom 0 +
        q.negOnePow • (ιTensorObj K (power K n) _ _ _ _).hom 0 = 0
      simp only [map_zero, smul_zero, add_zero]

/-- 全二色語の和は、元の同次反復入力の二項展開そのもの。 -/
lemma mayColoredValue_sum (K : Complex k) (q : ℤ) (a b : K.X q) (n : ℕ) :
    ∑ w : BinaryTensorWord n, mayColoredValue K q a b n w =
      mayRepeatedValue K q (a + b) n := by
  induction n with
  | zero =>
    change (∑ _ : PUnit, mayTensorUnitValue (k := k)) = mayTensorUnitValue
    exact Fintype.sum_unique _
  | succ n ih =>
    change (∑ w : BinaryTensorWord n ⊕ BinaryTensorWord n,
      mayColoredValue K q a b (n + 1) w) = _
    rw [Fintype.sum_sum_type]
    change (∑ w : BinaryTensorWord n,
        (ιTensorObj K (power K n) q (mayRepeatedDegree q n) _ rfl).hom
          (a ⊗ₜ[k] mayColoredValue K q a b n w)) +
      (∑ w : BinaryTensorWord n,
        (ιTensorObj K (power K n) q (mayRepeatedDegree q n) _ rfl).hom
          (b ⊗ₜ[k] mayColoredValue K q a b n w)) =
      (ιTensorObj K (power K n) q (mayRepeatedDegree q n) _ rfl).hom
        ((a + b) ⊗ₜ[k] mayRepeatedValue K q (a + b) n)
    rw [← map_sum, ← map_sum, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_sum,
      ih, TensorProduct.add_tmul, map_add]

end SerrePositivity.EInfinity.PowerOperation
