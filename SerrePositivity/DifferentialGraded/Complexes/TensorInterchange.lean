module
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous

/-! # tensorモノイダル関手の交差符号と既存shuffleの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- Mathlibのtensorμは既存の複体shuffleと同じ射。 -/
lemma tensorμ_eq_shuffle (P Q T U : Complex A) :
    tensorμ P Q T U = (SerrePositivity.cochainTensorShuffle P Q T U).hom := by
  simp only [tensorμ, SerrePositivity.cochainTensorShuffle, Iso.trans_hom]
  rfl

/-- 中央二因子の次数積がtensorμのKoszul符号になる。 -/
lemma tensorμ_apply (P Q T U : Complex A) (i j k l n : ℤ)
    (hn : i + j + k + l = n) (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (tensorμ P Q T U).f n
      (SerrePositivity.cochainTensorQuadι P Q T U i j k l n hn
        ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w))) =
      (j * k).negOnePow •
        SerrePositivity.cochainTensorQuadι P T Q U i k j l n (by omega)
          ((x ⊗ₜ[A] z) ⊗ₜ[A] (y ⊗ₜ[A] w)) := by
  rw [tensorμ_eq_shuffle]
  exact SerrePositivity.cochainTensorShuffle_hom_apply_ι P Q T U i j k l n hn x y z w

end SerrePositivity.DifferentialGraded
