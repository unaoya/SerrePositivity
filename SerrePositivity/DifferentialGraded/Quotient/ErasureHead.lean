module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureMiddleInterchange
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # 左端εの消去と中間消去のtensor表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左端のεを消し、単位因子も除く次数+1のcochain。 -/
def eraseHead (P : Complex A) : Cochain (epsilonComplex A ⊗ P) P 1 :=
  (eraseRightTensor A P).comp (Cochain.ofHom (λ_ P).hom) (add_zero 1)

lemma eraseHead_closed (P : Complex A) : δ 1 2 (eraseHead A P) = 0 := by
  rw [eraseHead, δ_comp_ofHom, eraseRightTensor_closed]
  exact Cochain.zero_comp _ _

/-- 中間ε消去は左端ε消去を左tensorしたものに等しい。 -/
lemma eraseMiddle_eq_tensorLeft (K P : Complex A) :
    eraseMiddle A K P = (tensorLeftHom K (epsilonComplex A ⊗ P) P).f 1 (eraseHead A P) := by
  rw [eraseHead, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  rfl

/-- 前方二因子のchain mapによる合成は、その後のε消去と可換する。 -/
lemma tensorJoin_eraseMiddle (U V W P : Complex A) (c : U ⊗ V ⟶ W) :
    (Cochain.ofHom ((α_ U V (epsilonComplex A ⊗ P)).inv ≫ c ▷ (epsilonComplex A ⊗ P))).comp
      (eraseMiddle A W P) (zero_add 1) =
    ((tensorLeftHom U (V ⊗ (epsilonComplex A ⊗ P)) (V ⊗ P)).f 1
      (eraseMiddle A V P)).comp
      (Cochain.ofHom ((α_ U V P).inv ≫ c ▷ P)) (add_zero 1) := by
  simpa only [← eraseMiddle_eq_tensorLeft] using
    tensorJoin_cochain_naturality U V W (epsilonComplex A ⊗ P) P c 1 (eraseHead A P)

end SerrePositivity.DifferentialGraded.DGQuotient
