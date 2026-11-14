module

public import Mathlib.Algebra.Category.Ring.Basic
public import SerrePositivity.AlgebraicGeometry.ReducedResidueProduct
public import SerrePositivity.AlgebraicGeometry.IntegralClosureProductFields

/-!
概要：被約環の単射整拡大で、極小素イデアル集合が準コンパクトな被約環を供給する。
方針：全剰余体の積への標準埋め込みを取り、その積の中の整閉包を使う。
規約：Noether 性、有限個の極小素イデアル、非自明性は仮定しない。
使われ方：Rydh 3.10 の非 Noether affine 基底の証明で必要な、TIC の代わりの供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u

/-- 被約環は、被約かつ極小素イデアル集合が準コンパクトな環へ単射かつ整に拡大できる。
Rydh 3.10 で使う TIC の性質のみを供給し、TIC 全体の構造は主張しない。 -/
theorem exists_integral_injective_reduced_compact_minimalPrimes
    (A : CommRingCat.{u}) [IsReduced A] :
    ∃ (B : CommRingCat.{u}) (i : A →+* B),
      IsReduced B ∧ Function.Injective i ∧ i.IsIntegral ∧
        IsCompact {q : PrimeSpectrum B | q.asIdeal ∈ minimalPrimes B} := by
  let K := ResidueFieldProduct A
  let : Algebra A K := (reducedResidueProductMap A).toAlgebra
  let B := integralClosure A K
  have hB : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  refine ⟨CommRingCat.of B, algebraMap A B, hB, ?_, ?_, ?_⟩
  · intro a b hab
    apply reducedResidueProductMap_injective A
    exact congrArg (fun x : B ↦ (x : K)) hab
  · exact algebraMap_isIntegral_iff.mpr inferInstance
  · exact isCompact_minimalPrimes_integralClosure_productFields
      (A := A) (fun q : PrimeSpectrum A ↦ q.asIdeal.ResidueField)

end SerrePositivity.AlgebraicGeometry
