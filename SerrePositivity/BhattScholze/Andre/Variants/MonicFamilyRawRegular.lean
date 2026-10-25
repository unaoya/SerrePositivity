module

public import SerrePositivity.BhattScholze.Andre.Variants.MonicFamilyPowerResidue
public import SerrePositivity.BhattScholze.Andre.Variants.MonicRawPDivision
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootFiniteRawRegular
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaAdjoinDivisionFamilyRegular
public import SerrePositivity.CommutativeAlgebra.WittGhostInjective

/-!
# André E1・E2：任意モニック族の raw δ p 除算包の p 正則性

## 概要

p 正則な δ 係数環上の独立変数ごとの任意モニック関係族について、各関係の
Frobenius 像を同時に p で除算した raw 環で p は非零因子となる。
BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の補助計算に対応する。

## 方針

有限先行族の関係の p 乗商での正則性により一入力追加の帰納を行う。
ghost 単射を p 正則性から内部で供給し、有限部分族の既存余極限で任意族へ移す。

## 規約

δ(p) は単元と仮定する。正次数は不要で、係数環や族の有限性も要求しない。
これは補助 φ/p 包の p 正則性であり、f/d 包やその perfectoid 商の忠実平坦性ではない。

## 使われ方

任意モニック関係族に対する pd 比較と実導来 p 完備化の入力に用いる。
-/

@[expose] public noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime]

/-- 概要：p 正則な係数環上の相対自由 δ 源では ghost 射が単射。
方針：多項式環の自由性で p 正則性を移し G4 を適用する。
規約：添字の有限性は不要。
使われ方：BS Cor 2.39（著者版 p.25）の有限族帰納の ghost 入力。 -/
private theorem sourceGhost_injective {S : Type u} [CommRing S]
    (hpS : Function.Injective (fun x : S => (p : S) * x)) (ι : Type v) :
    Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := S) ι) → ℕ → RelativeFreeDeltaRing (R := S) ι) := by
  apply witt_ghostMap_injective_of_mul_prime_injective
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular S (p : S) from hpS).of_flat
      (S := RelativeFreeDeltaRing (R := S) ι)

variable {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => fun s : σ => monicRelation (f s) s

/-- 概要：任意有限部分族のモニック関係の raw φ/p 包は p 正則。
方針：先行 p 乗商の後続正則性で一入力追加を帰納し、ghost 単射を G4 から供給する。
規約：モニック関係の次数は正でなくてもよい。
使われ方：BS Cor 2.39（著者版 p.25）の有限独立関係族の raw 計算。 -/
theorem monicFiniteRaw_p_mul_injective (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) (T : Finset σ) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P)
      (fun s : T => DeltaStructure.frobeniusLift E (r s)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun s : T => DeltaStructure.frobeniusLift E (r s))) * x) := by
  classical
  have hpP : Function.Injective (fun x : P => (p : P) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  obtain ⟨w, hw⟩ := hdp
  let wP := Units.map (MvPolynomial.C : A →+* P).toMonoidHom w
  have hwP : (wP : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  induction T using Finset.induction_on with
  | empty =>
    let e := deltaAdjoinDivisionEmptyEquiv E (p : P)
      (fun s : (∅ : Finset σ) => DeltaStructure.frobeniusLift E (r s))
    intro x y hxy
    apply e.injective
    apply hpP
    simpa only [map_mul, map_natCast] using congrArg e hxy
  | @insert s T hs ih =>
    have hx : IsSMulRegular
        (P ⧸ deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T => r t ^ p))
        (Ideal.Quotient.mk
          (deltaDivisionFirstBaseIdeal (p := p) (p : P) (fun t : T => r t ^ p)) (r s)) := by
      have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
        congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
      rw [deltaDivisionFirstBaseIdeal, hpp]
      exact polynomialSubsetPowerModP_remaining_isSMulRegular (T : Set σ) f p (f s) (hf s) s hs
    have hstep := deltaPDivisionFamilySum_p_mul_injective (η := PUnit.{max u v + 1}) E
      (fun t : T => r t) (r s) hpP ih (sourceGhost_injective hpP T)
      (sourceGhost_injective ih PUnit.{max u v + 1}) wP hwP hx
    let ρ := deltaRootFiniteInsertIndexEquiv (η := PUnit.{max u v + 1}) T s hs
    let e := deltaAdjoinDivisionReindexEquiv E (p : P)
      (Sum.elim (fun t : T => DeltaStructure.frobeniusLift E (r t))
        (fun _ : PUnit.{max u v + 1} => DeltaStructure.frobeniusLift E (r s)))
      (fun t : (insert s T : Finset σ) => DeltaStructure.frobeniusLift E (r t)) ρ
      (fun t => by cases t <;> rfl)
    intro x y hxy
    apply e.symm.injective
    apply hstep
    simpa only [map_mul, map_natCast] using congrArg e.symm hxy

/-- 概要：任意個の独立モニック関係の raw φ/p 包は p 正則。
方針：すべての有限部分族の p 正則性を既存の有限部分族余極限で移す。
規約：族の濃度に制限を置かず、遷移射の単射性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の任意根族への補助 raw 計算。 -/
theorem monicFamilyRaw_p_mul_injective (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hdp : D.IsDistinguished (p : A)) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P)
      (fun s : σ => DeltaStructure.frobeniusLift E (r s)) =>
      (p : DeltaAdjoinDivision E (p : P)
        (fun s : σ => DeltaStructure.frobeniusLift E (r s))) * x) := by
  apply deltaAdjoinDivisionFamily_p_mul_injective E (p : P)
    (fun s : σ => DeltaStructure.frobeniusLift E (r s))
  intro T
  exact monicFiniteRaw_p_mul_injective D f hf hpA hdp T

/-- 概要：完全 prism 上の任意モニック族の補助 raw φ/p 包は p 正則。
方針：完全 δ 構造から係数環の p 正則性と p 完備性を取り出し、任意族版に適用する。
規約：prism の商の p 正則性や最終候補の忠実平坦性は結論しない。
使われ方：BS Rem 7.15（著者版 p.62）の pd 比較の raw 正則性入力。 -/
theorem perfectPrismMonicFamilyRaw_p_mul_injective
    (P₀ : OrientedPrism p A) (hP : P₀.deltaStructure.IsPerfect)
    (f : σ → Polynomial A) (hf : ∀ s, (f s).Monic) :
    Function.Injective (fun x : DeltaAdjoinDivision
      (polynomialRankOneDeltaStructure σ P₀.deltaStructure) (p : MvPolynomial σ A)
      (fun s : σ => (polynomialRankOneDeltaStructure σ P₀.deltaStructure).frobeniusLift
        (monicRelation (f s) s)) =>
      (p : DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ P₀.deltaStructure)
        (p : MvPolynomial σ A)
        (fun s : σ => (polynomialRankOneDeltaStructure σ P₀.deltaStructure).frobeniusLift
          (monicRelation (f s) s))) * x) := by
  let := P₀.isAdicComplete_p_of_perfect hP
  apply monicFamilyRaw_p_mul_injective P₀.deltaStructure f hf hP.p_mul_injective
  exact DeltaStructure.isDistinguished_p P₀.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre
