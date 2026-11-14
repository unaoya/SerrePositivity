module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedPermutation

/-!
# May の同次混合入力の最初の交換

May, Proposition 2.3(ii) の符号の前段。
二つの同じ次数の入力は異なってよく、残りの同次テンソルは任意とする。
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

/-- 異なる二入力でも、同じ次数なら同じ Koszul 符号で交換される。 -/
lemma mayHomogeneousSwapFirst (K : Complex k) (q : ℤ) (a b : K.X q) (n : ℕ)
    (y : (power K n).X (mayRepeatedDegree q n)) :
    (swapFirstIso K n).hom.f (mayRepeatedDegree q (n + 2))
      (ιTensorObj K (cochainTensor K (power K n)) q (mayRepeatedDegree q (n + 1))
        (mayRepeatedDegree q (n + 2)) rfl
        (a ⊗ₜ[k] (ιTensorObj K (power K n) q (mayRepeatedDegree q n)
          (mayRepeatedDegree q (n + 1)) rfl (b ⊗ₜ[k] y)))) =
    (q * q).negOnePow •
      (ιTensorObj K (cochainTensor K (power K n)) q (mayRepeatedDegree q (n + 1))
        (mayRepeatedDegree q (n + 2)) rfl
        (b ⊗ₜ[k] (ιTensorObj K (power K n) q (mayRepeatedDegree q n)
          (mayRepeatedDegree q (n + 1)) rfl (a ⊗ₜ[k] y)))) := by
  change (cochainTensorAssociator K K (power K n)).hom.f (q + (q + mayRepeatedDegree q n))
    ((cochainTensorMap (cochainTensorSymmetry K K).hom (𝟙 (power K n))).f _
      ((cochainTensorAssociator K K (power K n)).inv.f _
        (ιTensorObj K (cochainTensor K (power K n)) q (q + mayRepeatedDegree q n)
          (q + (q + mayRepeatedDegree q n)) rfl
          (a ⊗ₜ[k] (ιTensorObj K (power K n) q (mayRepeatedDegree q n)
            (q + mayRepeatedDegree q n) rfl (b ⊗ₜ[k] y)))))) = _
  rw [cochainTensorAssociator_inv_apply_ι_of_sum, cochainTensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [cochainTensorSymmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul']
  change ((cochainTensorAssociator K K (power K n)).hom.f _).hom
    ((ιTensorObj (cochainTensor K K) (power K n) _ _ _ _).hom
      ((↑(q * q).negOnePow : ℤ) • _)) = _
  rw [map_zsmul, map_zsmul, cochainTensorAssociator_hom_apply_ι]
  rfl

end SerrePositivity.EInfinity.PowerOperation
