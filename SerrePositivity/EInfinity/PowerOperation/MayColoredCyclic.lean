module

public import SerrePositivity.EInfinity.PowerOperation.MayColoredPermutation
public import SerrePositivity.EInfinity.PowerOperation.MayCyclicInputInvariant

/-!
# May の混合入力の巡回置換

May, Proposition 2.3(ii) の軌道表示の前段。
同次二色語の全置換の符号を計算し、標数 p の p 巡回作用では符号が消える。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
variable {k : Type u} [CommRing k]

/-- 同次二色入力の全置換は、同じ語の置換と実 Koszul 符号になる。 -/
lemma mayColoredValue_permutation (K : Complex k) (q : ℤ) (a b : K.X q)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : BinaryTensorWord n) :
    (permutationAction K n σ).asIso.hom.f (mayRepeatedDegree q n)
      (mayColoredValue K q a b n w) =
        (Equiv.Perm.sign σ ^ (q * q)) • mayColoredValue K q a b n (σ • w) := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [permutationAction_one, Equiv.Perm.sign_one, one_zpow, one_smul, one_smul]
    rfl
  | succ n =>
    have hs : σ ∈ Submonoid.closure (Set.range (@adjacentTransposition n)) := by
      rw [show (@adjacentTransposition n) =
        (fun i : Fin n => Equiv.swap i.castSucc i.succ) from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hs using Submonoid.closure_induction generalizing w with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      have he : Equiv.Perm.sign (adjacentTransposition i) = -1 :=
        Equiv.Perm.sign_swap i.castSucc_lt_succ.ne
      rw [he, permutationAction_adjacent]
      exact mayColoredValue_adjacent K q a b n i w
    | one =>
      rw [permutationAction_one, Equiv.Perm.sign_one, one_zpow, one_smul, one_smul]
      rfl
    | mul σ τ _ _ hσ hτ =>
      rw [permutationAction_mul]
      change (permutationAction K (n + 1) σ).asIso.hom.f _
        ((permutationAction K (n + 1) τ).asIso.hom.f _
          (mayColoredValue K q a b (n + 1) w)) = _
      rw [hτ w]
      change ((permutationAction K (n + 1) σ).asIso.hom.f _).hom
        (_ • mayColoredValue K q a b (n + 1) (τ • w)) = _
      simp only [Units.smul_def, map_zsmul]
      rw [hσ (τ • w), ← mul_smul σ τ w]
      simp only [Units.smul_def, smul_smul, Equiv.Perm.sign_mul, mul_zpow, Units.val_mul]
      rw [mul_comm]

/-- 標数 p の同次二色入力では、p 巡回置換の実符号は消える。 -/
lemma mayColoredValue_cyclic (p : ℕ) [NeZero p] [Fact p.Prime] [CharP k p]
    (K : Complex k) (q : ℤ) (a b : K.X q) (g : MayCyclicGroup.{u} p)
    (w : BinaryTensorWord p) :
    (permutationAction K p g.val.down).asIso.hom.f (mayRepeatedDegree q p)
      (mayColoredValue K q a b p w) = mayColoredValue K q a b p (g.val.down • w) := by
  rw [mayColoredValue_permutation]
  rcases (Fact.out : p.Prime).eq_two_or_odd' with hp | hp
  · subst p
    exact mayIntegerUnit_smul_charTwo (k := k) _ _
  · rw [mayCyclicSign_odd p hp g, one_zpow, one_smul]

end SerrePositivity.EInfinity.PowerOperation
