module

public import SerrePositivity.HomologicalAlgebra.AdicFilteredComplex
public import SerrePositivity.CommutativeAlgebra.HilbertSamuelBasic

/-! # adic フィルトレーション商の有限長性

一般の部分複体の構成に Noether 局所環の準素条件を適用する。
フィルトレーションと quasi-isomorphism の一般論はホモロジー代数側に置く。
-/

@[expose] public section
universe u
namespace SerrePositivity.AdicFilteredComplex
open CategoryTheory CategoryTheory.Limits IsLocalRing
variable {R : Type u} [CommRing R]
variable (P : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R)
variable (hd : ∀ q, (P.d q (q + 1)).hom.range ≤ I • ⊤)

/-- 準素イデアルと有限生成の項から、adic 商の各項の有限長性を得る。 -/
theorem finiteLength_quotient_term [IsNoetherianRing R] [IsLocalRing R]
    (hI : I.radical = maximalIdeal R) (q n : ℤ) [Module.Finite R (P.X q)] :
    IsFiniteLength R ((quotient P I hd n).X q) :=
  Module.length_ne_top_iff.mp (HilbertSamuel.samuelFunction_ne_top R I hI (P.X q) (n + q).toNat)

end SerrePositivity.AdicFilteredComplex
