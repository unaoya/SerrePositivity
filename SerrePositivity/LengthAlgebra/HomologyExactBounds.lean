module

public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Homology.HomologySequence

/-! # 短完全列のホモロジーの長さと誤差評価

長完全列の二つの部分から両方向の長さの上界を導く。
値は ℝ≥0∞ のままで扱い、有限性や完全複体の仮定は要求しない。
-/

@[expose] public section
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 短完全列の中央のホモロジーの長さは両端の和以下。
ホモロジーの長完全列と、冪ねじれ加群上の長さの劣加法性を使う。 -/
lemma lambdaHomology_shortExact_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q)) :
    lam.len (S.X₂.homology q) ≤ lam.len (S.X₁.homology q) + lam.len (S.X₃.homology q) :=
  lam.len_le_add_of_exact (HomologicalComplex.homologyMap S.f q).hom
    (HomologicalComplex.homologyMap S.g q).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₂ q).moduleCat_range_eq_ker.symm) t₁ t₂ t₃

/-- 左のホモロジーの長さは、余核の一つ前の次数と中央の同次数の和以下。 -/
theorem lambdaHomology_shortExact_left_le
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₃prev : IsPowTorsion J (S.X₃.homology (q - 1)))
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q)) :
    lam.len (S.X₁.homology q) ≤ lam.len (S.X₃.homology (q - 1)) +
      lam.len (S.X₂.homology q) := by
  have hrel : (ComplexShape.up ℤ).Rel (q - 1) q := by simp
  exact lam.len_le_add_of_exact (hS.δ (q - 1) q hrel).hom
    (HomologicalComplex.homologyMap S.f q).hom
    (LinearMap.exact_iff.mpr (hS.homology_exact₁ (q - 1) q hrel).moduleCat_range_eq_ker.symm)
    t₃prev t₁ t₂

/-- 誤差複体の隣接する二次数の長さが零なら、比較するホモロジーの長さは一致。
比較する長さが有限であるという追加仮定は不要。 -/
theorem lambdaHomology_shortExact_eq_of_error_zero
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) (q : ℤ)
    (t₁ : IsPowTorsion J (S.X₁.homology q))
    (t₂ : IsPowTorsion J (S.X₂.homology q))
    (t₃ : IsPowTorsion J (S.X₃.homology q))
    (t₃prev : IsPowTorsion J (S.X₃.homology (q - 1)))
    (hprev : lam.len (S.X₃.homology (q - 1)) = 0)
    (hcurrent : lam.len (S.X₃.homology q) = 0) :
    lam.len (S.X₁.homology q) = lam.len (S.X₂.homology q) := by
  apply le_antisymm
  · simpa only [hprev, zero_add] using
      lambdaHomology_shortExact_left_le lam S hS q t₃prev t₁ t₂
  · simpa only [hcurrent, add_zero] using
      lambdaHomology_shortExact_le lam S hS q t₁ t₂ t₃

end SerrePositivity
