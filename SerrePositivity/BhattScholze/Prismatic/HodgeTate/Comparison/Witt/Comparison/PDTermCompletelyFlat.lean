module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 小さい完備分冪模型の完全平坦性

## 概要
p 正則な基底上で、小さい完備分冪模型の各項は (p) 完全平坦。

## 方針
未完備模型の単項式基底と、既存の主完備化の完全忠実平坦性を合成する。

## 規約
基底の p 正則性を明記する。完備化した環の通常の平坦性は主張しない。

## 使われ方
BS 著者版 Theorem 6.4 の完備分冪項の導来係数変更の検査。
-/

public noncomputable section

open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem completion_completelyFlat (p : ℕ) (k R : Type u)
    [CommRing k] [CommRing R] [Algebra k R]
    (hflat : IsCompletelyFlat (Ideal.span {(p : k)}) R)
    (hbound : ∃ N : ℕ, ∀ (j : ℕ) (x : R),
      (p : R) ^ j • x = 0 → (p : R) ^ N • x = 0) :
    letI := principalCompletionCommRing R (p : R)
    letI := ((principalCompletionUnitRingHom R (p : R)).comp (algebraMap k R)).toAlgebra
    IsCompletelyFlat (Ideal.span {(p : k)}) (PrincipalCompletionH0 R (p : R)) := by
  let D := PrincipalCompletionH0 R (p : R)
  let := principalCompletionCommRing R (p : R)
  let f : k →+* R := algebraMap k R
  let g : R →+* D := principalCompletionUnitRingHom R (p : R)
  have hg : g.toAlgebra = principalCompletionAlgebra R (p : R) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hc : @IsCompletelyFlat R _ ((Ideal.span {(p : k)}).map f) D _
      g.toAlgebra.toModule := by
    rw [hg, Ideal.map_span, Set.image_singleton, map_natCast]
    exact (Andre.Transfinite.principalCompletionH0_isCompletelyFaithfullyFlat R (p : R) hbound).1
  have hf : f.toAlgebra = (inferInstance : Algebra k R) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have hf' : @IsCompletelyFlat k _ (Ideal.span {(p : k)}) R _ f.toAlgebra.toModule := by
    rw [hf]
    exact hflat
  exact Andre.Transfinite.isCompletelyFlat_comp f g (Ideal.span {(p : k)}) hf' hc

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)
variable (hreg : Function.Injective (fun x : k => (p : k) * x))

include hreg in
/-- p 正則基底上の小さい完備分冪項は (p) 完全平坦。 -/
theorem pdTerm_completelyFlat : IsCompletelyFlat (Ideal.span {(p : k)}) (pdTerm p k r n) := by
  let R := pdRaw k r n
  let : Module.Free k R := Module.Free.of_basis (pdRawBasis k r n)
  have hflat : IsCompletelyFlat (Ideal.span {(p : k)}) R := by
    let : Module.Flat k R := inferInstance
    intro M _ _ _
    apply (isConcentratedInDegreeZero_derivedTensor_iff R M).mpr
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact torModule_subsingleton_of_flat R M j
  have hR : IsSMulRegular R (p : R) := PDSmallRawEnvelope.raw_regular p r n hreg
  have hbound : ∃ N : ℕ, ∀ (j : ℕ) (x : R),
      (p : R) ^ j • x = 0 → (p : R) ^ N • x = 0 := by
    refine ⟨0, fun j x hx => ?_⟩
    have hz : x = 0 := (hR.pow j) (by simpa only [smul_zero] using hx)
    simp only [pow_zero, one_smul, hz]
  exact completion_completelyFlat p k R hflat hbound

end SerrePositivity.BhattScholze.Prismatic
