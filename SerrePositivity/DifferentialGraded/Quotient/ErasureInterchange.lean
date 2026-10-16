module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonTensor
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange

/-! # ε消去と後方cochainの反交換

単位因子を除く前のε消去について、右隣の次数+1 cochainと順序交換すると負号が付く。
任意の非有界複体を前に置いても、この反交換式は全次数tensor写像で保存される。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- ε消去と右隣の次数+1 cochainの反交換。 -/
lemma eraseRightTensor_tail_anticommute (P Q : Complex A) (f : Cochain P Q 1) :
    (eraseRightTensor A P).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom (epsilonComplex A) P Q).f 1 f).comp (eraseRightTensor A Q)
      (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorCochain_odd_anticommute (epsilonComplex A) (𝟙_ (Complex A)) P Q (eraseEpsilon A) f

/-- 任意の前方因子でtensorした後も、ε消去と後方cochainは反交換する。 -/
lemma eraseRightTensor_prefixed_anticommute (K P Q : Complex A) (f : Cochain P Q 1) :
    ((tensorLeftHom K (epsilonComplex A ⊗ P) (𝟙_ (Complex A) ⊗ P)).f 1
      (eraseRightTensor A P)).comp
      ((tensorLeftHom K (𝟙_ (Complex A) ⊗ P) (𝟙_ (Complex A) ⊗ Q)).f 1
        ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 1 f))
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 1
      ((tensorLeftHom (epsilonComplex A) P Q).f 1 f)).comp
      ((tensorLeftHom K (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)).f 1
        (eraseRightTensor A Q)) (show (1 : ℤ) + 1 = 2 by omega)) :=
  tensorLeftHom_cochain_anticommute K _ _ _ _ 1 1 2 (by omega) (by omega)
    _ _ _ _ (eraseRightTensor_tail_anticommute A P Q f)

end SerrePositivity.DifferentialGraded.DGQuotient
