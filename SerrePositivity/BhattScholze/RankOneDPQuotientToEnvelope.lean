module

public import SerrePositivity.BhattScholze.RankOneDPTruncationQuotient
public import SerrePositivity.BhattScholze.RankOneDPEnvelopeFree
public import Mathlib.RingTheory.AlgebraTower

/-! # 実商B/(y^p)から通常分冪添加環への自由・忠実平坦な実射 -/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra rankOneDPPolynomialQuotientAlgebra
variable {p : ℕ} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra (Polynomial A) B]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)
local notation "DA" => DividedPowerAlgebra A A
local notation "Q₀" => B ⧸ Ideal.span {(algebraMap P₀ B Polynomial.X) ^ p}
local notation "U₀" => RankOneDPBaseChangedTruncation p A B
local notation "D₀" => RankOneDPBaseChangedEnvelope A B

/-- 実商からの、全代表元bを1⊗bへ送る実環射。 -/
def rankOneDPQuotientToEnvelope (hpos : 0 < p) (hp : (p : A) = 0) : Q₀ →+* D₀ := by
  letI : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  letI : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  exact (rankOneDPEnvelopeBaseChangeMap hpos hp).toRingHom.comp
    (rankOneDPTruncationQuotientEquiv (A := A) (B := B) p).toRingHom

/-- 実商からの環射の、全代表元上の具体式。 -/
theorem rankOneDPQuotientToEnvelope_mk (hpos : 0 < p) (hp : (p : A) = 0) (b : B) :
    rankOneDPQuotientToEnvelope hpos hp (Ideal.Quotient.mk _ b) = (1 : DA) ⊗ₜ[P₀] b := by
  let : Algebra C₀ DA := rankOneDPTruncatedAlgebra hpos hp
  let : IsScalarTower P₀ C₀ DA := rankOneDPPolynomial_truncated_isScalarTower hpos hp
  change rankOneDPEnvelopeBaseChangeMap hpos hp
    (rankOneDPTruncationQuotientEquiv (A := A) p (Ideal.Quotient.mk _ b)) = _
  rw [rankOneDPTruncationQuotientEquiv_mk, rankOneDPEnvelopeBaseChangeMap_tmul, map_one]

/-- 実商同型による、Uの具体的な商環上のスカラー作用。 -/
abbrev rankOneDPTruncationQuotientAlgebra : Algebra Q₀ U₀ :=
  (rankOneDPTruncationQuotientEquiv (A := A) (B := B) p).toRingHom.toAlgebra

/-- 実商から分冪添加環への指定した射による具体的代数構造。 -/
abbrev rankOneDPQuotientToEnvelopeAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra Q₀ D₀ :=
  (rankOneDPQuotientToEnvelope (B := B) hpos hp).toAlgebra

/-- 実商からUを経由する指定されたスカラー塔。 -/
theorem rankOneDPQuotientToEnvelope_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
    letI : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
    IsScalarTower Q₀ U₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hpos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- 指定された実射について、通常分冪添加環はB/(y^p)上自由。 -/
theorem rankOneDPQuotientToEnvelope_moduleFree (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.Free Q₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower Q₀ U₀ D₀ := rankOneDPQuotientToEnvelope_isScalarTower hprime.pos hp
  let e : Q₀ ≃ₐ[Q₀] U₀ :=
    { __ := rankOneDPTruncationQuotientEquiv (A := A) (B := B) p
      commutes' := fun _ ↦ rfl }
  let b : Module.Basis Unit Q₀ U₀ := (Module.Basis.singleton Unit Q₀).map e.toLinearEquiv
  exact Module.Free.of_basis (b.smulTower (rankOneDPEnvelopeBasis hprime hp))

/-- 指定された実射について、通常分冪添加環はB/(y^p)上平坦。 -/
theorem rankOneDPQuotientToEnvelope_moduleFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.Flat Q₀ D₀ := by
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : Module.Free Q₀ D₀ := rankOneDPQuotientToEnvelope_moduleFree hprime hp
  infer_instance

/-- 指定された実射について、通常分冪添加環はB/(y^p)上忠実平坦。零環も含む。 -/
theorem rankOneDPQuotientToEnvelope_moduleFaithfullyFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    letI : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
    Module.FaithfullyFlat Q₀ D₀ := by
  let : Algebra Q₀ U₀ := rankOneDPTruncationQuotientAlgebra (p := p) (A := A) (B := B)
  let : Algebra U₀ D₀ := rankOneDPEnvelopeBaseChangedAlgebra hprime.pos hp
  let : Algebra Q₀ D₀ := rankOneDPQuotientToEnvelopeAlgebra hprime.pos hp
  let : IsScalarTower Q₀ U₀ D₀ := rankOneDPQuotientToEnvelope_isScalarTower hprime.pos hp
  let e : Q₀ ≃ₐ[Q₀] U₀ :=
    { __ := rankOneDPTruncationQuotientEquiv (A := A) (B := B) p
      commutes' := fun _ ↦ rfl }
  let : Module.FaithfullyFlat Q₀ U₀ :=
    Module.FaithfullyFlat.of_linearEquiv Q₀ Q₀ e.symm.toLinearEquiv
  let : Module.FaithfullyFlat U₀ D₀ := rankOneDPEnvelope_moduleFaithfullyFlat hprime hp
  exact Module.FaithfullyFlat.trans Q₀ U₀ D₀

end SerrePositivity.BhattScholze
