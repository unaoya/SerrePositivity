module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedCycles
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import Mathlib.GroupTheory.Perm.Sign

/-!
# May の反復同次入力の隣接交換

May, Definition 2.1 の巡回作用の照合に使う Koszul 符号。
同じ次数 q の二因子の交換は (−1)^{q*q} を掛ける。
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

/-- 同次反復入力の最初の二因子を交換した際の実 Koszul 符号。 -/
lemma mayRepeatedValue_swapFirst (K : Complex k) (q : ℤ) (a : K.X q) (n : ℕ) :
    (swapFirstIso K n).hom.f (mayRepeatedDegree q (n + 2))
      (mayRepeatedValue K q a (n + 2)) =
        (q * q).negOnePow • mayRepeatedValue K q a (n + 2) := by
  change (cochainTensorAssociator K K (power K n)).hom.f (q + (q + mayRepeatedDegree q n))
    ((cochainTensorMap (cochainTensorSymmetry K K).hom (𝟙 (power K n))).f _
      ((cochainTensorAssociator K K (power K n)).inv.f _
        (ιTensorObj K (cochainTensor K (power K n)) q (q + mayRepeatedDegree q n)
          (q + (q + mayRepeatedDegree q n)) rfl
          (a ⊗ₜ[k] (ιTensorObj K (power K n) q (mayRepeatedDegree q n)
            (q + mayRepeatedDegree q n) rfl
            (a ⊗ₜ[k] mayRepeatedValue K q a n)))))) = _
  rw [cochainTensorAssociator_inv_apply_ι_of_sum, cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul']
  change ((cochainTensorAssociator K K (power K n)).hom.f _).hom
    ((ιTensorObj (cochainTensor K K) (power K n) _ _ _ _).hom
      ((↑(q * q).negOnePow : ℤ) • _)) = _
  rw [map_zsmul, map_zsmul, cochainTensorAssociator_hom_apply_ι]
  rfl

/-- どの隣接位置でも同じ Koszul 符号になる。 -/
lemma mayRepeatedValue_adjacent (K : Complex k) (q : ℤ) (a : K.X q)
    (n : ℕ) (i : Fin n) :
    (adjacentIso K n i).hom.f (mayRepeatedDegree q (n + 1))
      (mayRepeatedValue K q a (n + 1)) =
        (q * q).negOnePow • mayRepeatedValue K q a (n + 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact mayRepeatedValue_swapFirst K q a n
    · change (cochainTensorMap (𝟙 K) (adjacentIso K n j).hom).f _
        (ιTensorObj K (power K (n + 1)) q (mayRepeatedDegree q (n + 1)) _ rfl
          (a ⊗ₜ[k] mayRepeatedValue K q a (n + 1))) = _
      rw [cochainTensorMap_apply_ι]
      simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
      rw [ih j]
      simp only [Units.smul_def, TensorProduct.tmul_smul]
      change (ιTensorObj K (power K (n + 1)) _ _ _ _).hom
        ((↑(q * q).negOnePow : ℤ) • _) = _
      rw [map_zsmul]
      rfl

/-- 任意の置換が同次反復入力に作用する際の実符号。 -/
lemma mayRepeatedValue_permutation (K : Complex k) (q : ℤ) (a : K.X q)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationAction K n σ).asIso.hom.f (mayRepeatedDegree q n)
      (mayRepeatedValue K q a n) =
        (Equiv.Perm.sign σ ^ (q * q)) • mayRepeatedValue K q a n := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [permutationAction_one, Equiv.Perm.sign_one, one_zpow, one_smul]
    rfl
  | succ n =>
    have hs : σ ∈ Submonoid.closure
        (Set.range (@SerrePositivity.Coxeter.adjacentTransposition n)) := by
      rw [show (@SerrePositivity.Coxeter.adjacentTransposition n) =
        (fun i : Fin n => Equiv.swap i.castSucc i.succ) from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hs using Submonoid.closure_induction with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      have he : Equiv.Perm.sign (SerrePositivity.Coxeter.adjacentTransposition i) = -1 := by
        apply Equiv.Perm.sign_swap
        exact i.castSucc_lt_succ.ne
      rw [he, permutationAction_adjacent]
      change (adjacentIso K n i).hom.f _ (mayRepeatedValue K q a (n + 1)) = _
      exact mayRepeatedValue_adjacent K q a n i
    | one =>
      rw [permutationAction_one, Equiv.Perm.sign_one, one_zpow, one_smul]
      rfl
    | mul σ τ _ _ hσ hτ =>
      rw [permutationAction_mul]
      change (permutationAction K (n + 1) σ).asIso.hom.f _
        ((permutationAction K (n + 1) τ).asIso.hom.f _
          (mayRepeatedValue K q a (n + 1))) = _
      rw [hτ]
      change ((permutationAction K (n + 1) σ).asIso.hom.f _).hom
        (_ • mayRepeatedValue K q a (n + 1)) = _
      simp only [Units.smul_def, map_zsmul]
      rw [hσ]
      simp only [Units.smul_def, smul_smul, Equiv.Perm.sign_mul, mul_zpow, Units.val_mul]
      rw [mul_comm]

end SerrePositivity.EInfinity.PowerOperation
