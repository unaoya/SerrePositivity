module

public import SerrePositivity.EInfinity.PowerOperation.MayUnitEvaluation

/-!
# May の零次反復入力と単位射の反復入力

May, Proposition 2.3(iii) の零次照合の補助。
同じ指定元の反復を零次へ移し、単位からの同じ射を全入力へ入れた値と比較する。
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

lemma mayRepeatedZeroDegree (n : ℕ) : mayRepeatedDegree 0 n = 0 := by
  rw [mayRepeatedDegree_eq, mul_zero]

/-- 零次にある同じ反復入力を、全次数の等式だけで零次成分へ移す。 -/
def mayRepeatedZeroValue (K : Complex k) (a : K.X 0) (n : ℕ) : (power K n).X 0 :=
  (eqToHom (congrArg (fun i : ℤ => (power K n).X i) (mayRepeatedZeroDegree n))).hom
    (mayRepeatedValue K 0 a n)

lemma mayTensorZeroDegree_transport (K L : Complex k) (j : ℤ) (hj : j = 0)
    (a : K.X 0) (b : L.X j) :
    (eqToHom (congrArg (fun i : ℤ => (cochainTensor K L).X i)
      ((zero_add j).trans hj))).hom
        (ιTensorObj K L 0 j (0 + j) rfl (a ⊗ₜ[k] b)) =
      ιTensorObj K L 0 0 0 rfl
        (a ⊗ₜ[k] (eqToHom (congrArg (fun i : ℤ => L.X i) hj)).hom b) := by
  subst j
  rfl

lemma mayRepeatedZeroValue_succ (K : Complex k) (a : K.X 0) (n : ℕ) :
    mayRepeatedZeroValue K a (n + 1) =
      ιTensorObj K (power K n) 0 0 0 rfl (a ⊗ₜ[k] mayRepeatedZeroValue K a n) := by
  exact mayTensorZeroDegree_transport K (power K n) (mayRepeatedDegree 0 n)
    (mayRepeatedZeroDegree n) a (mayRepeatedValue K 0 a n)

/-- 同じ零次の指定元での、反復した単位射と同次反復入力の一致。 -/
lemma mayRepeatedUnitInput_value {K : Complex k} (f : 𝟙_ (Complex k) ⟶ K) (n : ℕ) :
    (repeatedUnitInput f n).f 0 (mayTensorUnitValue (k := k)) =
      mayRepeatedZeroValue K (f.f 0 (mayTensorUnitValue (k := k))) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cochainTensorMap f (repeatedUnitInput f n)).f 0
      ((λ_ (𝟙_ (Complex k))).inv.f 0 (mayTensorUnitValue (k := k))) = _
    rw [mayUnitLeftInverse_value, cochainTensorMap_apply_ι, mayRepeatedZeroValue_succ, ih]

end SerrePositivity.EInfinity.PowerOperation
