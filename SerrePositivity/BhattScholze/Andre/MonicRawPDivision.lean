module

public import SerrePositivity.BhattScholze.Andre.MonicRelationResidue
public import SerrePositivity.BhattScholze.DeltaPDivisionRawRegular
public import SerrePositivity.BhattScholze.PolynomialRankOneDelta
public import SerrePositivity.BhattScholze.PerfectOrientedPrism
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-!
# André E1：一元モニック関係の raw δ p 除算包の p 正則性

## 概要

モニック多項式を独立変数で評価した y に対し、raw δ 環の `φ(y)/p` 添加で
p は非零因子となる。BS 著者版 Cor 2.39（p.25）の一元入力に対応する。

## 方針

モニック性から mod p 正則性を供給し、既存の任意正則元の raw p 除算定理を適用する。
ghost 単射は係数環の p 正則性から多項式環の自由性と G4 により供給する。

## 規約

これは補助的な `φ(y)/p` 計算であり、一般 d による `y/d` 包そのものの平坦性ではない。
正次数はこの p 正則性には不要。prismatic envelope の比較は別工程。

## 使われ方

BS Rem 7.15（著者版 p.62）の pd 計算と δ 除算の比較への正則入力。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A τ : Type u} [CommRing A]

local notation "B" => MvPolynomial τ A

/-- 概要：p 正則な δ 係数環と単元 δ(p) の下で、一元モニック関係の raw p 除算包は p 正則。
方針：mod p のモニック正則性を既存 raw 包定理へ渡し、ghost 単射を内部で供給する。
規約：モニック f の正次数は不要である。
使われ方：BS Cor 2.39（著者版 p.25）の補助 p 除算計算。 -/
theorem monicRawPDivision_p_mul_injective
    (D : DeltaStructure p A) (f : Polynomial A) (hf : f.Monic) (s : τ)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) :
    Function.Injective (fun x : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ D)
      (p : B) (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ D).frobeniusLift
        (monicRelation f s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ D)
        (p : B) (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ D).frobeniusLift
          (monicRelation f s))) * x) := by
  let E := polynomialRankOneDeltaStructure τ D
  let L := RelativeFreeDeltaRing (R := B) PUnit.{u + 1}
  have hpB : Function.Injective (fun x : B => (p : B) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := B)
  have hg : Function.Injective (WittVector.ghostMap : WittVector p L → ℕ → L) := by
    apply witt_ghostMap_injective_of_mul_prime_injective
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular B (p : B) from hpB).of_flat (S := L)
  obtain ⟨v, hv⟩ := hdp
  let w := Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* B)) v
  have hw : (w : B) = E.delta (p : B) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, ← polynomialRankOneDeltaStructure_delta_C τ D (p : A), map_natCast]
  exact deltaPDivisionRaw_p_mul_injective (σ := PUnit.{u + 1}) E (monicRelation f s)
    hpB hg w hw (monicRelation_modP_isSMulRegular p f hf s)

/-- 概要：完全 prism 上では一元モニック関係の raw φ/p 包は p 正則。
方針：完全 δ 構造の p 正則性と p 完備性から前定理の入力を供給する。
規約：prism の商の p ねじれなしは主張しない。
使われ方：BS Rem 7.15（著者版 p.62）の補助 p 除算計算の具体的入力。 -/
theorem perfectPrismMonicRawPDivision_p_mul_injective
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (f : Polynomial A) (hf : f.Monic) (s : τ) :
    Function.Injective (fun x : DeltaAdjoinDivision
      (polynomialRankOneDeltaStructure τ P.deltaStructure) (p : B)
      (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ P.deltaStructure).frobeniusLift
        (monicRelation f s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure τ P.deltaStructure) (p : B)
        (fun _ : PUnit.{u + 1} => (polynomialRankOneDeltaStructure τ P.deltaStructure).frobeniusLift
          (monicRelation f s))) * x) := by
  let := P.isAdicComplete_p_of_perfect hP
  apply monicRawPDivision_p_mul_injective P.deltaStructure f hf s hP.p_mul_injective
  exact DeltaStructure.isDistinguished_p P.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre
