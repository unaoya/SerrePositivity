module

public import SerrePositivity.EInfinity.PowerOperation.TensorPowerRepresentation
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Bounds

/-!
# 同じ p 入力の上界

DAG XIII Construction 2.2.6 の完全入力を上有界係数模型へ送るための補助。
同じテンソル冪の上界を加え、指定された作用を付けても上界を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {k : Type u} [CommRing k]

/-- 同じテンソル冪の上界は、元の上界の n 倍。 -/
lemma tensorPower_isStrictlyLE (K : Complex k) (a : ℤ) [K.IsStrictlyLE a] (n : ℕ) :
    (power K n).IsStrictlyLE (n * a) := by
  induction n with
  | zero =>
    simp only [power, Nat.cast_zero, zero_mul]
    change ((singleFunctor (ModuleCat k) 0).obj (ModuleCat.of k k)).IsStrictlyLE 0
    infer_instance
  | succ n ih =>
    have := ih
    change (cochainTensor K (power K n)).IsStrictlyLE ((n + 1 : ℕ) * a)
    have h := cochainTensor_isStrictlyLE K (power K n) a (n * a)
    simpa only [power, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h

/-- 同じ複体に作用を付けた表現複体は上界を保つ。 -/
lemma representationCochainComplex_isStrictlyLE {G : Type u} [Group G]
    (K : Complex k) (ρ : G →* End K) (a : ℤ) [K.IsStrictlyLE a] :
    (representationCochainComplex ρ).IsStrictlyLE a := by
  rw [isStrictlyLE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  apply (forget₂ (Rep.{u} k G) (ModuleCat k)).map_injective
  change (𝟙 (K.X i)) = 0
  exact (K.isZero_of_isStrictlyLE a i hi).eq_of_src _ _

/-- 同じ置換作用を付けた n 入力は、上界 n a を持つ。 -/
lemma tensorPowerRepresentation_isStrictlyLE {G : Type u} [Group G]
    (K : Complex k) (n : ℕ) (σ : G →* Equiv.Perm (Fin n)) (a : ℤ) [K.IsStrictlyLE a] :
    ((tensorPowerRepresentationFunctor n σ).obj K).IsStrictlyLE (n * a) := by
  have := tensorPower_isStrictlyLE K a n
  exact representationCochainComplex_isStrictlyLE _ (tensorPowerComplexAction K n σ) _

end SerrePositivity.EInfinity.PowerOperation
