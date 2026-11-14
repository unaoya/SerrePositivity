module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedInput
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-!
# May の同次入力の反復テンソル

May, Definition 2.1 の e_i ⊗ a^{⊗p} に使う a^{⊗p} を、元の全複体で作る。
全整数の余鎖次数を許し、閉入力の反復が閉じることと厳密射での自然性を保持する。
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

/-- 元のテンソル単位の零次の指定元。 -/
def mayTensorUnitValue : (𝟙_ (Complex k)).X 0 :=
  (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat k))).inv (1 : k)

/-- 右括弧の反復入力の全次数。 -/
def mayRepeatedDegree (q : ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => q + mayRepeatedDegree q n

lemma mayRepeatedDegree_eq (q : ℤ) (n : ℕ) :
    mayRepeatedDegree q n = (n : ℤ) * q := by
  induction n with
  | zero => simp [mayRepeatedDegree]
  | succ n ih => simp only [mayRepeatedDegree, ih, Nat.cast_add, Nat.cast_one]; ring

/-- 同じ次数 q の入力を n 個テンソルする。全次数は n*q。 -/
def mayRepeatedValue (K : Complex k) (q : ℤ) (a : K.X q) :
    (n : ℕ) → (power K n).X (mayRepeatedDegree q n)
  | 0 => mayTensorUnitValue (k := k)
  | n + 1 => ιTensorObj K (power K n) q (mayRepeatedDegree q n) (mayRepeatedDegree q (n + 1))
      rfl (a ⊗ₜ[k] mayRepeatedValue K q a n)

/-- 閉じた同次入力の全反復は、元のテンソル複体でも閉じる。 -/
lemma mayRepeatedValue_cycle (K : Complex k) (q : ℤ) (a : K.X q)
    (ha : K.d q (q + 1) a = 0) (n : ℕ) :
    (power K n).d (mayRepeatedDegree q n) (mayRepeatedDegree q n + 1)
      (mayRepeatedValue K q a n) = 0 := by
  induction n with
  | zero =>
    change (𝟙_ (Complex k)).d 0 1 (mayTensorUnitValue (k := k)) = 0
    have hd : (𝟙_ (Complex k)).d 0 1 = 0 := rfl
    rw [hd]
    rfl
  | succ n ih =>
    change (cochainTensor K (power K n)).d _ _
      (ιTensorObj K (power K n) _ _ _ _ (a ⊗ₜ[k] mayRepeatedValue K q a n)) = 0
    rw [cochainTensor_d_apply_ι, ha, ih]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    change (ιTensorObj K (power K n) _ _ _ _).hom 0 +
      q.negOnePow • (ιTensorObj K (power K n) _ _ _ _).hom 0 = 0
    simp only [map_zero, smul_zero, add_zero]

/-- 同じ反復元は任意の厳密な複体射に自然。 -/
lemma mayRepeatedValue_naturality {K L : Complex k} (f : K ⟶ L)
    (q : ℤ) (a : K.X q) (n : ℕ) :
    (TensorPowers.map f n).f (mayRepeatedDegree q n) (mayRepeatedValue K q a n) =
      mayRepeatedValue L q (f.f q a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cochainTensorMap f (TensorPowers.map f n)).f _
      (ιTensorObj K (power K n) _ _ _ _ (a ⊗ₜ[k] mayRepeatedValue K q a n)) = _
    rw [cochainTensorMap_apply_ι, ih]
    rfl

end SerrePositivity.EInfinity.PowerOperation
