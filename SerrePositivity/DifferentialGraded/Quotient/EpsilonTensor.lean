module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonDifferential
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightHom

/-! # ε消去cochainのtensorによる拡張

左の因子を通る際のKoszul符号は主Homのtensor写像で与える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左に任意非有界複体を置いたε消去。 -/
def eraseLeftTensor (P : Complex A) : Cochain (P ⊗ epsilonComplex A) (P ⊗ 𝟙_ (Complex A)) 1 :=
  (tensorLeftHom P (epsilonComplex A) (𝟙_ (Complex A))).f 1 (eraseEpsilon A)

lemma eraseLeftTensor_closed (P : Complex A) : δ 1 2 (eraseLeftTensor A P) = 0 :=
  homComplexMap_closed (tensorLeftHom P (epsilonComplex A) (𝟙_ (Complex A)))
    1 (eraseEpsilon A) (eraseEpsilon_closed A)

/-- 右に任意非有界複体を置いたε消去。 -/
def eraseRightTensor (P : Complex A) : Cochain (epsilonComplex A ⊗ P) (𝟙_ (Complex A) ⊗ P) 1 :=
  (tensorRightHom P (epsilonComplex A) (𝟙_ (Complex A))).f 1 (eraseEpsilon A)

lemma eraseRightTensor_closed (P : Complex A) : δ 1 2 (eraseRightTensor A P) = 0 :=
  homComplexMap_closed (tensorRightHom P (epsilonComplex A) (𝟙_ (Complex A)))
    1 (eraseEpsilon A) (eraseEpsilon_closed A)

/-- 左因子の次数iを通るε消去には(-1)^iが付く。 -/
lemma eraseLeftTensor_apply (P : Complex A) (i a n : ℤ)
    (ha : i + (-1) = a) (hn : a + 1 = n) (x : P.X i) (e : (epsilonComplex A).X (-1)) :
    (eraseLeftTensor A P).v a n hn
      (ιTensorObj P (epsilonComplex A) i (-1) a ha (x ⊗ₜ[A] e)) =
    i.negOnePow • ιTensorObj P (𝟙_ (Complex A)) i 0 n (by omega)
      (x ⊗ₜ[A] (eraseEpsilon A).v (-1) 0 (by omega) e) := by
  simpa only [eraseLeftTensor, one_mul] using
    (tensorLeftHom_apply_of_sum P (epsilonComplex A) (𝟙_ (Complex A)) 1 i (-1) a 0 n
      ha (by omega) hn
      (eraseEpsilon A) x e)

/-- 右因子を置く場合は追加の符号を持たない。 -/
lemma eraseRightTensor_apply (P : Complex A) (j a n : ℤ)
    (ha : (-1) + j = a) (hn : a + 1 = n) (e : (epsilonComplex A).X (-1)) (x : P.X j) :
    (eraseRightTensor A P).v a n hn
      (ιTensorObj (epsilonComplex A) P (-1) j a ha (e ⊗ₜ[A] x)) =
    ιTensorObj (𝟙_ (Complex A)) P 0 j n (by omega)
      ((eraseEpsilon A).v (-1) 0 (by omega) e ⊗ₜ[A] x) := by
  exact tensorRightHom_apply P (epsilonComplex A) (𝟙_ (Complex A))
    1 (-1) j a n ha hn (eraseEpsilon A) e x

/-- P⊗(ε⊗Q)からP⊗Qへの次数+1の消去。 -/
def eraseMiddle (P Q : Complex A) : Cochain (P ⊗ (epsilonComplex A ⊗ Q)) (P ⊗ Q) 1 :=
  ((tensorLeftHom P (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
    (eraseRightTensor A Q)).comp (Cochain.ofHom (P ◁ (λ_ Q).hom)) (add_zero 1)

/-- 中間のε消去は内部微分と反交換する。 -/
lemma eraseMiddle_closed (P Q : Complex A) : δ 1 2 (eraseMiddle A P Q) = 0 := by
  rw [eraseMiddle, δ_comp_ofHom]
  have h : δ 1 2
      ((tensorLeftHom P (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
        (eraseRightTensor A Q)) = 0 :=
    homComplexMap_closed _ 1 _ (eraseRightTensor_closed A Q)
  rw [h]
  exact Cochain.zero_comp _ _

end SerrePositivity.DifferentialGraded.DGQuotient
