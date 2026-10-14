module

public import SerrePositivity.FieldTheory.PBasisCofiniteField
public import SerrePositivity.CommutativeAlgebra.PrimaryCompletedDifferential

/-! # 中間係数体上の完備微分の有限生成性

有限個のp-basis方向を残す係数体から、元の係数体への有限性を供給する。
Mathlibの中間体の係数制限とスカラー塔を用い、準素商の有限性を移す。
-/

@[expose] public section
universe u
namespace SerrePositivity
open IsLocalRing

/-- 共通剰余体を持つ準素商の有限性を、中間係数体へ制限する。 -/
theorem IsPBasis.moduleFinite_primaryQuotient_cofiniteField
    {K S : Type u} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [IsLocalRing S]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue S).comp (algebraMap K S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite (pBasisCofiniteField (p := p) b e) (S ⧸ I) := by
  let E := pBasisCofiniteField (p := p) b e
  let : Module.Finite E K := hb.finite_cofiniteField e
  let : Module.Finite K (S ⧸ I) := finite_quotient_of_common_residue_primary hres I hI
  exact Module.Finite.trans K _

/-- 準素なパラメータの閉ファイバーは各中間係数体上でも有限。
従って、その係数体上の完備微分も有限生成。 -/
theorem IsPBasis.moduleFinite_completedKaehler_cofiniteField
    {K S : Type u} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    {p : ℕ} [Fact p.Prime] [CharP K p] {ι : Type*} {b : ι → K}
    (hb : IsPBasis K p b) (e : Finset ι)
    (hres : Function.Surjective ((residue S).comp (algebraMap K S)))
    (I : Ideal S) (hI : I.radical = maximalIdeal S) :
    Module.Finite S (AdicCompletion I
      (KaehlerDifferential (pBasisCofiniteField (p := p) b e) S)) := by
  let E := pBasisCofiniteField (p := p) b e
  let : Module.Finite E (S ⧸ I) := hb.moduleFinite_primaryQuotient_cofiniteField e hres I hI
  have hIm : I ≤ maximalIdeal S := by rw [← hI]; exact Ideal.le_radical
  let : IsAdicComplete I S := isAdicComplete_finite_of_le_maximalIdeal I hIm
  exact moduleFinite_completedKaehler_of_finiteType_fiber I I.fg_of_isNoetherianRing

end SerrePositivity
