module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
public import SerrePositivity.HomologicalAlgebra.Tor
import all SerrePositivity.BhattScholze.Delta.DividedPower.Frobenius.FrobeniusDivisionRegularSequence
import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaFrobeniusFlat
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.LocalizedTor
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# 自由 Frobenius 除算の高次 Tor

## 概要
BS 著者版 Remark 2.37 の二脚を、任意の添字型の自由 δ 座標に対して記述する。

## 方針
Frobenius の p 完全平坦性と、p を逆にした後で p 倍への評価が可逆になることを使う。

## 規約
通常の可換環上の Tor で述べる。

## 使われ方
自由 Frobenius 除算の通常の押し出しの計算。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

universe u v

namespace SerrePositivity.BhattScholze

open scoped TensorProduct

section Localization

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (D : DeltaStructure p R)
    (σ : Type v)

local notation "P" => RelativeFreeDeltaRing (R := R) σ
local notation "E" => relativeFreeDeltaStructure σ D
local notation "Lₚ" => Localization.Away (p : P)
local notation "α" => deltaDivisionSourceMap (σ := σ) D (p : R)
local notation "j" => algebraMap P Lₚ

private theorem primePowers_stable (x : Submonoid.powers (p : P)) :
    (E).frobeniusLift x ∈ Submonoid.powers (p : P) := by
  obtain ⟨n, hn⟩ := x.property
  exact ⟨n, by rw [← hn, map_pow, map_natCast]⟩

private theorem relativeFreeDeltaHom_ext {B : Type*} [CommRing B]
    (G : DeltaStructure p B) (f g : P →+* B)
    (hf : (E).IsDeltaHom G f) (hg : (E).IsDeltaHom G g)
    (hC : f.comp MvPolynomial.C = g.comp MvPolynomial.C)
    (hX : ∀ s : σ, f (MvPolynomial.X (s, 0)) = g (MvPolynomial.X (s, 0))) : f = g := by
  apply MvPolynomial.ringHom_ext' hC
  rintro ⟨s, n⟩
  rw [relativeFreeDeltaHom_X_iterates D G f hf, relativeFreeDeltaHom_X_iterates D G g hg, hX]

private theorem primeDivision_localized_flat : ((j).comp α).Flat := by
  let M := Submonoid.powers (p : P)
  let G := (E).localization M Lₚ (primePowers_stable D σ)
  have hj : (E).IsDeltaHom G j := (E).isDeltaHom_localization M Lₚ (primePowers_stable D σ)
  have hα := deltaDivisionSourceMap_isDeltaHom (σ := σ) D (p : R)
  let c : R →+* Lₚ := (j).comp MvPolynomial.C
  let v : Lₚ := IsLocalization.Away.invSelf (p : P)
  have hv : (p : Lₚ) * v = 1 := by
    rw [← map_natCast j]
    exact IsLocalization.Away.mul_invSelf (S := Lₚ) (p : P)
  let β : P →+* Lₚ := relativeFreeDeltaEval G c (fun s : σ ↦ v * j (MvPolynomial.X (s, 0)))
  have hβ : (E).IsDeltaHom G β := relativeFreeDeltaEval_isDeltaHom D G c
    (hj.comp (relativeFreeDeltaStructure_C_isDeltaHom σ D)) _
  have hu (f : P →+* Lₚ) (m : M) : IsUnit (f m) := by
    obtain ⟨n, hn⟩ := m.property
    rw [← hn, map_pow, map_natCast, ← map_natCast j]
    exact (IsLocalization.map_units Lₚ (⟨(p : P), Submonoid.mem_powers _⟩ : M)).pow n
  obtain ⟨a, ha, _⟩ := (E).existsUnique_localization_lift M Lₚ (primePowers_stable D σ)
    G ((j).comp α) (hj.comp hα) (hu ((j).comp α))
  obtain ⟨b, hb, _⟩ := (E).existsUnique_localization_lift M Lₚ (primePowers_stable D σ)
    G β hβ (hu β)
  have ha' (x : P) : a (j x) = j (α x) := DFunLike.congr_fun ha.1 x
  have hb' (x : P) : b (j x) = β x := DFunLike.congr_fun hb.1 x
  have haX (s : σ) : a (j (MvPolynomial.X (s, 0))) = (p : Lₚ) * j (MvPolynomial.X (s, 0)) := by
    rw [ha', deltaDivisionSourceMap_X]
    simp
  have hbX (s : σ) : b (j (MvPolynomial.X (s, 0))) = v * j (MvPolynomial.X (s, 0)) := by
    rw [hb']
    simp [β]
  have hav : a v = v := by
    have he := congrArg a hv
    rw [map_mul, map_natCast, map_one] at he
    have hp : IsUnit (p : Lₚ) := by
      rw [← map_natCast j]
      exact IsLocalization.map_units Lₚ (⟨(p : P), Submonoid.mem_powers _⟩ : M)
    exact hp.mul_left_cancel (he.trans hv.symm)
  have hab : a.comp b = RingHom.id Lₚ := by
    apply IsLocalization.ringHom_ext M
    apply relativeFreeDeltaHom_ext D σ G _ _ (ha.2.comp (hb.2.comp hj)) hj
    · ext r
      change a (b (j (MvPolynomial.C r))) = j (MvPolynomial.C r)
      rw [hb', show β (MvPolynomial.C r) = j (MvPolynomial.C r) from
        relativeFreeDeltaEval_C _ _ _ _, ha', deltaDivisionSourceMap_C]
    · intro s
      change a (b (j (MvPolynomial.X (s, 0)))) = j (MvPolynomial.X (s, 0))
      rw [hbX, map_mul, hav, haX, ← mul_assoc, mul_comm v, hv, one_mul]
  have hba : b.comp a = RingHom.id Lₚ := by
    apply IsLocalization.ringHom_ext M
    apply relativeFreeDeltaHom_ext D σ G _ _ (hb.2.comp (ha.2.comp hj)) hj
    · ext r
      change b (a (j (MvPolynomial.C r))) = j (MvPolynomial.C r)
      rw [ha', deltaDivisionSourceMap_C, hb']
      exact relativeFreeDeltaEval_C _ _ _ _
    · intro s
      change b (a (j (MvPolynomial.X (s, 0)))) = j (MvPolynomial.X (s, 0))
      rw [haX, map_mul, map_natCast, hbX, ← mul_assoc, hv, one_mul]
  rw [← ha.1]
  have hjFlat : (j).Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Lₚ M)
  exact hjFlat.comp (RingHom.Flat.of_bijective (RingEquiv.ofRingHom a b hab hba).bijective)

end Localization


section PrimeLocal

open CategoryTheory

variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 概要：p 局所整数上の自由 δ 環。
方針：自由 δ 座標を `σ × ℕ` で添字付けする。
規約：BS 著者版 Remark 2.37 の押し出しの三つの自由環は同じ台環を使う。
使われ方：Frobenius と p 倍への評価を二脚とする押し出し。 -/
abbrev PrimeLocalFreeDeltaRing := RelativeFreeDeltaRing (R := PrimeLocalInt p) σ

local notation "P" => PrimeLocalFreeDeltaRing p σ
local notation "E" => relativeFreeDeltaStructure σ (primeLocalIntDelta p)
local notation "φ" => DeltaStructure.frobeniusLift E
local notation "α" =>
  deltaDivisionSourceMap (σ := σ) (primeLocalIntDelta p) (p : PrimeLocalInt p)

private theorem primeLocalFreeDeltaRing_p_regular : IsSMulRegular P (p : P) := by
  have hp : IsSMulRegular (PrimeLocalInt p) (p : PrimeLocalInt p) := by
    have h := IsSMulRegular.of_isLocalization (PrimeLocalInt p)
      (Ideal.span {(p : ℤ)}).primeCompl (x := (p : ℤ)) (by
        intro x y h
        exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) h)
    rwa [map_natCast (algebraMap ℤ (PrimeLocalInt p))] at h
  exact polynomial_primeRegular (p := p) (σ := σ × ℕ) hp

private theorem primePolynomial_frobenius_flat (τ : Type u) :
    (frobenius (MvPolynomial τ (ZMod p)) p).Flat := by
  let K := MvPolynomial τ (ZMod p)
  let L := PolynomialExpandTarget p τ (ZMod p)
  let e : L ≃+* K := ULift.ringEquiv
  let f := e.symm.toRingHom.comp (frobenius K p)
  have hf : f.Flat := by
    let : Algebra K L := f.toAlgebra
    change Module.Flat K L
    have := primePolynomial_frobenius_moduleFaithfullyFlat p τ
    infer_instance
  have he : e.toRingHom.comp f = frobenius K p := by
    apply RingHom.ext
    intro a
    exact e.apply_symm_apply _
  rw [← he]
  exact hf.comp (RingHom.Flat.of_bijective e.bijective)

private theorem primeLocalFreeDelta_modPrime_frobenius_flat : (modPMap p φ).Flat := by
  let Q := ModP P p
  let I := Ideal.span {(p : P)}
  let q : P →+* Q := Ideal.Quotient.mk I
  let K := MvPolynomial (σ × ℕ) (ZMod p)
  let e : Q ≃+* K := (polynomialModPrimeEquiv (p := p) (σ × ℕ)).trans
    (MvPolynomial.mapEquiv _ (primeLocalIntModPrimeEquiv p))
  have he : e.toRingHom.comp (modPMap p φ) = (frobenius K p).comp e.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    change e (q (φ a)) = (e (q a)) ^ p
    rw [(E).map_frobeniusLift_of_map_p_eq_zero q (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))), map_pow]
  have he' : modPMap p φ = e.symm.toRingHom.comp ((frobenius K p).comp e.toRingHom) := by
    rw [← he]
    apply RingHom.ext
    intro a
    exact (e.symm_apply_apply _).symm
  rw [he']
  exact ((RingHom.Flat.of_bijective e.bijective).comp
    (primePolynomial_frobenius_flat p (σ × ℕ))).comp
    (RingHom.Flat.of_bijective e.symm.bijective)

private theorem primeLocalFreeDelta_frobenius_isCompletelyFlat :
    IsCompletelyFlat (Ideal.span {(p : P)}) (baseChangeScalarModule φ) := by
  let T := ULift.{0} P
  let eT : T ≃+* P := ULift.ringEquiv
  let f := eT.symm.toRingHom.comp φ
  let : Algebra P T := f.toAlgebra
  let : Module P T := f.toAlgebra.toModule
  let : SMul P T := f.toAlgebra.toModule.toSMul
  let I := Ideal.span {(p : P)}
  apply isCompletelyFlat_of_linearEquiv I
    (M := T) (N := baseChangeScalarModule φ)
    { eT.toAddEquiv with
      map_smul' := by
        intro r x
        change eT (r • x) = φ r * eT x
        rw [Algebra.smul_def, map_mul]
        rfl }
  have hp := primeLocalFreeDeltaRing_p_regular p σ
  have hT : IsSMulRegular T (p : P) := by
    intro x y h
    apply eT.injective
    apply hp
    change (p : P) * eT x = (p : P) * eT y
    have he : eT (algebraMap P T (p : P)) = (p : P) := by
      rw [map_natCast, map_natCast]
    change (algebraMap P T (p : P)) * x = (algebraMap P T (p : P)) * y at h
    simpa only [map_mul, he] using congrArg (fun z : T ↦ eT z) h
  apply isCompletelyFlat_principal_of_regular (p : P) hp T hT
  let J := I.map (algebraMap P T)
  have hJ : J = I.map eT.symm.toRingHom := by
    change I.map (algebraMap P T) = I.map eT.symm.toRingHom
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      map_natCast, map_natCast]
  let eQ := Ideal.quotientEquiv I J eT.symm hJ
  let g := algebraMap (P ⧸ I) (T ⧸ J)
  have hg : g = eQ.toRingHom.comp (modPMap p φ) := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    rfl
  have hflat : g.Flat := hg ▸ (primeLocalFreeDelta_modPrime_frobenius_flat p σ).comp
    (RingHom.Flat.of_bijective eQ.bijective)
  have : Module.Flat (P ⧸ I) (T ⧸ J) := RingHom.flat_algebraMap_iff.mp hflat
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T I).symm.toLinearEquiv

end PrimeLocal

private theorem torAlg_subsingleton_of_regular_away_flat {R : Type u} [CommRing R]
    (a : R) (F α : R →+* R) (hα : α a = a)
    (ha : IsSMulRegular R a)
    (hF : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule F))
    (hflat : ((algebraMap R (Localization.Away a)).comp α).Flat) (i : ℕ) :
    Subsingleton (TorAlg F (i + 1) (baseChangeScalarModule α)) := by
  let S := Localization.Away a
  let j : R →+* S := algebraMap R S
  have hu : IsUnit (j a) :=
    IsLocalization.map_units S (⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers a)
  have hsurj (y : S) : ∃ (n : ℕ) (x : R), j (a ^ n) * y = j x := by
    let t := IsLocalization.Away.sec a y
    exact ⟨t.2, t.1, (mul_comm _ _).trans (IsLocalization.Away.sec_spec a y)⟩
  have hzero (x : R) (hx : j x = 0) : ∃ n : ℕ, a ^ n * x = 0 := by
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a) S).mp
      (hx.trans (map_zero j).symm)
    exact ⟨n, by simpa only [mul_zero] using hn⟩
  let : Algebra R S := (j.comp α).toAlgebra
  let : Module R S := (j.comp α).toAlgebra.toModule
  let N := baseChangeScalarModule α
  let f : N →ₗ[R] S :=
    { toFun := fun x ↦ j (show R from x)
      map_add' := j.map_add
      map_smul' := fun r x ↦ by
        change j (α r * (show R from x)) = j (α r) * j (show R from x)
        exact map_mul j _ _ }
  have hloc : IsLocalizedModule (Submonoid.powers a) f := by
    apply IsLocalizedModule.Away.mk_of_addCommGroup
    · rw [Module.End.isUnit_iff]
      change Function.Bijective (fun x : S ↦ j (α a) * x)
      rw [hα]
      exact IsUnit.isUnit_iff_mulLeft_bijective.mp hu
    · intro y
      obtain ⟨n, x, hx⟩ := hsurj y
      refine ⟨n, (show N from x), ?_⟩
      change j (α (a ^ n)) * y = j x
      rwa [map_pow, hα]
    · intro x hx
      obtain ⟨n, hn⟩ := hzero (show R from x) hx
      refine ⟨n, ?_⟩
      change α (a ^ n) * (show R from x) = 0
      rwa [map_pow, hα]
  have : Module.Flat R S := hflat
  have hreg : IsSMulRegular N a := by
    intro x y h
    apply ha
    change α a * (show R from x) = α a * (show R from y) at h
    rwa [hα] at h
  have hz := torModule_subsingleton_of_completelyFlat_of_localizedModule_flat
    a (baseChangeScalarModule F) N S f hF hreg i
  let e := (scalarExtensionTorNatIso F (i + 1)).app N
  exact e.toLinearEquiv.injective.subsingleton

section PrimeLocal

open CategoryTheory

variable (p : ℕ) [Fact p.Prime] (σ : Type u)

local notation "P" => PrimeLocalFreeDeltaRing p σ
local notation "E" => relativeFreeDeltaStructure σ (primeLocalIntDelta p)
local notation "φ" => DeltaStructure.frobeniusLift E
local notation "α" =>
  deltaDivisionSourceMap (σ := σ) (primeLocalIntDelta p) (p : PrimeLocalInt p)

/-- 概要：自由 δ 環での Frobenius 除算の通常の押し出しは高次 Tor を持たない。
方針：φ 脚は p 完全平坦で、もう一方の脚は p を逆にすると同型。
規約：BS 著者版 Remark 2.37。φ 脚を係数拡大に用い、他方の脚は yₛ ↦ p zₛ。
使われ方：自由 Frobenius 除算の離散性の古典的な内容。 -/
theorem frobeniusDivisionPushout_torAlg_subsingleton (i : ℕ) :
    Subsingleton (TorAlg φ (i + 1) (baseChangeScalarModule α)) :=
  torAlg_subsingleton_of_regular_away_flat (p : P) φ α (map_natCast α p)
    (primeLocalFreeDeltaRing_p_regular p σ) (primeLocalFreeDelta_frobenius_isCompletelyFlat p σ)
    (primeDivision_localized_flat (primeLocalIntDelta p) σ) i


private theorem primeLocalInt_frobenius_eq_id :
    (primeLocalIntDelta p).frobeniusLift = RingHom.id (PrimeLocalInt p) :=
  IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

local notation "PZ" => RelativeFreeDeltaRing (R := P) σ
local notation "EZ" => relativeFreeDeltaStructure σ E
local notation "m" => MvPolynomial.map (σ := σ × ℕ) (MvPolynomial.C : PrimeLocalInt p →+* P)
local notation "b" => fun s : σ ↦ φ (MvPolynomial.X (s, 0))
local notation "αZ" => deltaDivisionSourceMap (σ := σ) E (p : P)
local notation "βZ" => deltaDivisionSourceEval E b

private theorem pushoutCoefficientMap_isDeltaHom : (E).IsDeltaHom EZ m := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro a
    rw [relativeFreeDeltaStructure_delta_C, MvPolynomial.map_C, MvPolynomial.map_C,
      relativeFreeDeltaStructure_delta_C, relativeFreeDeltaStructure_delta_C]
  · rintro ⟨s, n⟩
    rw [relativeFreeDeltaStructure_delta_X, MvPolynomial.map_X, MvPolynomial.map_X,
      relativeFreeDeltaStructure_delta_X]

private theorem pushoutCoefficientMap_comp : (αZ).comp m = (m).comp α := by
  have hm := pushoutCoefficientMap_isDeltaHom p σ
  apply relativeFreeDeltaHom_ext (primeLocalIntDelta p) σ EZ
  · exact (deltaDivisionSourceMap_isDeltaHom E (p : P)).comp hm
  · exact hm.comp (deltaDivisionSourceMap_isDeltaHom (primeLocalIntDelta p) (p : PrimeLocalInt p))
  · apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply, MvPolynomial.map_C, deltaDivisionSourceMap_C]
  · intro s
    simp only [RingHom.comp_apply, deltaDivisionSourceMap_X, Function.iterate_zero_apply,
      MvPolynomial.map_X, map_mul, map_natCast]

private theorem frobenius_C_primeLocal (r : PrimeLocalInt p) :
    φ (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [← (relativeFreeDeltaStructure_C_isDeltaHom σ (primeLocalIntDelta p)).map_frobeniusLift,
    primeLocalInt_frobenius_eq_id, RingHom.id_apply]

private theorem pushoutEvaluation_comp : (βZ).comp m = φ := by
  apply relativeFreeDeltaHom_ext (primeLocalIntDelta p) σ E
  · exact (deltaDivisionSourceEval_isDeltaHom E b).comp (pushoutCoefficientMap_isDeltaHom p σ)
  · exact DeltaStructure.isDeltaHom_frobeniusLift_general E
  · apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply, MvPolynomial.map_C, deltaDivisionSourceEval_C,
      frobenius_C_primeLocal]
  · intro s
    simp only [RingHom.comp_apply, MvPolynomial.map_X, deltaDivisionSourceEval_X,
      Function.iterate_zero_apply]

/-- 概要：自由 Frobenius 除算の生の環。
方針：各 `φ(xₛ)` を p で割る関係を δ 閉包で課す。
規約：BS 著者版 Remark 2.37。完備化の前の環。
使われ方：通常の押し出しおよびその零次の同定。 -/
abbrev FrobeniusDivisionPushoutRaw := DeltaAdjoinDivision E (p : P) b

local notation "C" => FrobeniusDivisionPushoutRaw p σ
local notation "J" =>
  (relativeFreeDeltaStructure σ E).deltaClosure (deltaDivisionRelationIdeal (p : P) b)
local notation "q" => Ideal.Quotient.mk J

/-- 自由 Frobenius 除算の x 脚からの標準射。 -/
abbrev frobeniusDivisionPushoutLeft : P →+* C := deltaAdjoinDivisionMap E (p : P) b

/-- 自由 Frobenius 除算の z 脚からの標準射。 -/
def frobeniusDivisionPushoutRight : P →+* C := (q).comp m

/-- 二つの標準射と Frobenius および p 倍評価が可換な四角をなす。 -/
theorem frobeniusDivisionPushout_square :
    (frobeniusDivisionPushoutRight p σ).comp α = (frobeniusDivisionPushoutLeft p σ).comp φ := by
  rw [frobeniusDivisionPushoutRight, RingHom.comp_assoc, ← pushoutCoefficientMap_comp,
    ← RingHom.comp_assoc, deltaDivisionSource_raw_square, RingHom.comp_assoc,
    pushoutEvaluation_comp]

/-- 概要：自由 Frobenius 除算の押し出しの零次は、生の δ 商で表される。
方針：係数環の自由変数を分け、既存の生の δ 除算包の押し出し普遍性を適用する。
規約：BS 著者版 Remark 2.37 の通常の可換環での普遍性。試験環に δ 構造を要求しない。
使われ方：高次 Tor の消滅と合わせた古典的押し出しの計算。 -/
theorem existsUnique_frobeniusDivisionPushoutLift {B : Type u} [CommRing B]
    (f g : P →+* B) (h : g.comp α = f.comp φ) :
    ∃! k : C →+* B, k.comp (frobeniusDivisionPushoutLeft p σ) = f ∧
      k.comp (frobeniusDivisionPushoutRight p σ) = g := by
  let G : PZ →+* B := MvPolynomial.eval₂Hom f (fun z ↦ g (MvPolynomial.X z))
  have hG : G.comp m = g := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hr := DFunLike.congr_fun h (MvPolynomial.C r)
      simp only [RingHom.comp_apply, deltaDivisionSourceMap_C, frobenius_C_primeLocal] at hr
      simp only [RingHom.comp_apply, MvPolynomial.map_C, G, MvPolynomial.eval₂Hom_C]
      exact hr.symm
    · intro z
      simp [G]
  have hG' : G.comp αZ = f.comp βZ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [G, deltaDivisionSourceMap_C, deltaDivisionSourceEval_C]
    · intro z
      let t := MvPolynomial.X z (R := PrimeLocalInt p)
      have ht : m t = MvPolynomial.X z := MvPolynomial.map_X _ _
      rw [RingHom.comp_apply, RingHom.comp_apply, ← ht]
      calc
        G (αZ (m t)) = g (α t) := by
          rw [show αZ (m t) = m (α t) from
            DFunLike.congr_fun (pushoutCoefficientMap_comp p σ) t]
          exact DFunLike.congr_fun hG _
        _ = f (φ t) := DFunLike.congr_fun h t
        _ = f (βZ (m t)) := congrArg f (DFunLike.congr_fun (pushoutEvaluation_comp p σ) t).symm
  obtain ⟨k, hk, hku⟩ := existsUnique_deltaDivisionSourceRawLift E (p : P) b f G hG'
  refine ⟨k, ⟨hk.2, ?_⟩, ?_⟩
  · rw [frobeniusDivisionPushoutRight, ← RingHom.comp_assoc, hk.1, hG]
  · intro l hl
    apply hku l
    refine ⟨?_, hl.1⟩
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, show G (MvPolynomial.C a) = f a by simp [G]]
      change l (frobeniusDivisionPushoutLeft p σ a) = f a
      exact DFunLike.congr_fun hl.1 a
    · intro z
      change l (q (MvPolynomial.X z)) = G (MvPolynomial.X z)
      rw [show G (MvPolynomial.X z) = g (MvPolynomial.X z) by simp [G]]
      have hz := DFunLike.congr_fun hl.2 (MvPolynomial.X z)
      simpa only [RingHom.comp_apply, frobeniusDivisionPushoutRight, MvPolynomial.map_X] using hz

end PrimeLocal

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.37" (partial := special) "導来 pushout の離散性を、通常の環での高次 Tor の消滅と零次の押し出しの同定として（単体的可換環としては述べない。BS-W15 K3） ／ 11-11 更新"] _root_.SerrePositivity.BhattScholze.existsUnique_frobeniusDivisionPushoutLift
attribute [cite BS19 "Rem 2.37" (partial := special) "導来 pushout の離散性を、通常の環での高次 Tor の消滅と零次の押し出しの同定として（単体的可換環としては述べない。BS-W15 K3） ／ 11-11 更新"] _root_.SerrePositivity.BhattScholze.frobeniusDivisionPushout_torAlg_subsingleton
