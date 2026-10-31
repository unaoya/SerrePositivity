module

public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Bounds
/-!
概要：交わらない上下界を持つ複体間の射と、下端の二変数積の零性を証明する。
方針：各次数で始域か終域が零であることと tensor の上界を使う。
規約：元の chain map の等式。使われ方：Postnikov 層の包含と平方零性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

variable {R : Type u} [CommRing R]

lemma cochainHom_eq_zero_of_bounds {P T : Complex R} (a b : ℤ)
    [P.IsStrictlyLE a] [T.IsStrictlyGE b] (hab : a < b) (f : P ⟶ T) : f = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : a < i
  · exact (P.isZero_of_isStrictlyLE a i hi).eq_of_src _ _
  · exact (T.isZero_of_isStrictlyGE b i (by omega)).eq_of_tgt _ _

lemma cochainBilinear_eq_zero_of_bounds {P Q T : Complex R} (a b c : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] [T.IsStrictlyGE c]
    (h : a + b < c) (f : P ⊗ Q ⟶ T) : f = 0 := by
  have : (P ⊗ Q).IsStrictlyLE (a + b) := by
    change (cochainTensor P Q).IsStrictlyLE (a + b)
    exact cochainTensor_isStrictlyLE P Q a b
  exact cochainHom_eq_zero_of_bounds (a + b) c h f

end SerrePositivity.KST.LocalizingInvariants
