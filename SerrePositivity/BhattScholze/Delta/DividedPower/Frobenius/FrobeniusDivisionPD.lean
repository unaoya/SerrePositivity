module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
public import SerrePositivity.BhattScholze.Delta.Division.BaseChange
public import SerrePositivity.BhattScholze.Delta.Division.Family
public import SerrePositivity.BhattScholze.Delta.Free.CrystallineTensorRegularity
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.Injectivity

/-!
# 自由 δ 座標の Frobenius 像の p 除算

## 概要
自由 δ 環で任意個の座標の Frobenius 像を p で割ると、生の包は p 正則。
p 局所な場合は階乗生成部分環と標準的に同型（BS 著者版 Lemma 2.36）。

## 方針
座標そのものの p 除算は自由 δ 環のまま。Frobenius に沿う押し出しで p 正則性を移す。

## 規約
自由 δ 座標とは多項式表示の反復次数 0 の変数。

## 使われ方
正則列に沿う分冪包と結晶サイトの自由枠。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace SerrePositivity.BhattScholze

section FreeCoordinates

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (D : DeltaStructure p R)
  (σ : Type v)

local notation "A" => RelativeFreeDeltaRing (R := R) σ
local notation "E" => relativeFreeDeltaStructure σ D
local notation "x" => (fun s : σ => (MvPolynomial.X (s, 0) : A))
local notation "B" => DeltaAdjoinDivision E (p : A) x
local notation "F" => deltaAdjoinDivisionStructure E (p : A) x
local notation "j" => deltaAdjoinDivisionMap E (p : A) x
local notation "z" => deltaAdjoinDivisionVariable E (p : A) x
local notation "C" => (MvPolynomial.C : R →+* A)

private theorem relativeFree_ext {T : Type*} [CommRing T] (G : DeltaStructure p T)
    (f g : A →+* T) (hf : (E).IsDeltaHom G f) (hg : (E).IsDeltaHom G g)
    (hC : f.comp C = g.comp C) (hX : ∀ s, f (x s) = g (x s)) : f = g := by
  apply MvPolynomial.ringHom_ext' hC
  rintro ⟨s, n⟩
  rw [relativeFreeDeltaHom_X_iterates D G f hf, relativeFreeDeltaHom_X_iterates D G g hg, hX s]

/-- 概要：自由 δ 座標そのものの p 除算環は、除算後の座標を変数とする自由 δ 環。
方針：元の自由座標を p 倍に写し、逆向きには各新座標を除算変数に写す。
規約：同型は係数上恒等（BS 著者版 Lemma 2.36 の押し出しの上の脚）。
使われ方：Frobenius 底変換の前の p 正則性。 -/
def freeCoordinatePDivisionEquiv : B ≃+* A := by
  let scale : A →+* A := relativeFreeDeltaEval E C (fun s => (p : A) * x s)
  have hscale : (E).IsDeltaHom E scale :=
    relativeFreeDeltaEval_isDeltaHom D E C (relativeFreeDeltaStructure_C_isDeltaHom σ D) _
  have hx (s : σ) : scale (x s) = (p : A) * x s := by simp [scale]
  let hf := existsUnique_deltaAdjoinDivisionHom E E (p : A) x scale hscale x
    (fun s => by rw [map_natCast, hx])
  let f := hf.choose
  obtain ⟨hfδ, hfj, hfz⟩ := hf.choose_spec.1
  let g : A →+* B := relativeFreeDeltaEval F ((j).comp C) z
  have hgδ : (E).IsDeltaHom F g :=
    relativeFreeDeltaEval_isDeltaHom D F ((j).comp C)
      ((deltaAdjoinDivisionMap_isDeltaHom E (p : A) x).comp
        (relativeFreeDeltaStructure_C_isDeltaHom σ D)) _
  have hgz (s : σ) : g (x s) = z s := by simp [g]
  have hgC (r : R) : g (C r) = j (C r) := relativeFreeDeltaEval_C F ((j).comp C) z r
  have hgj : g.comp scale = j := by
    apply relativeFree_ext D σ F _ _ (hgδ.comp hscale)
      (deltaAdjoinDivisionMap_isDeltaHom E (p : A) x)
    · apply RingHom.ext
      intro r
      change g (scale (C r)) = j (C r)
      rw [show scale (C r) = C r from relativeFreeDeltaEval_C _ _ _ _, hgC]
    · intro s
      change g (scale (x s)) = j (x s)
      rw [hx, map_mul, map_natCast, hgz, ← map_natCast j p]
      exact deltaAdjoinDivision_relation E (p : A) x s
  refine RingEquiv.ofRingHom f g ?_ ?_
  · apply relativeFree_ext D σ E _ _ (hfδ.comp hgδ) (fun _ => rfl)
    · apply RingHom.ext
      intro r
      change f (g (C r)) = C r
      rw [hgC, ← RingHom.comp_apply, hfj]
      exact relativeFreeDeltaEval_C _ _ _ _
    · intro s
      change f (g (x s)) = x s
      rw [hgz, hfz]
  · apply deltaAdjoinDivisionHom_ext E F (p : A) x _ _
      (hgδ.comp hfδ) (fun _ => rfl)
    · rw [RingHom.comp_assoc, hfj, hgj, RingHom.id_comp]
    · intro s
      change g (f (z s)) = z s
      rw [hfz, hgz]

end FreeCoordinates

section PrimeRegular

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] (D : DeltaStructure p R)
  (σ : Type u)

local notation "A" => RelativeFreeDeltaRing (R := R) σ
local notation "E" => relativeFreeDeltaStructure σ D
local notation "x" => (fun s : σ => (MvPolynomial.X (s, 0) : A))

set_option maxHeartbeats 3000000 in
/-- 概要：自由 δ 座標の Frobenius 像を p で割る生の包は p 正則。
方針：p 完全平坦な Frobenius に沿って自由座標の除算環を押し出す。
規約：自由 δ 環の mod p が素数体上の多項式環の場合（BS 著者版 Lemma 2.36）。
使われ方：p 局所な自由 δ 環での分冪模型との比較。 -/
theorem freeCoordinateFrobeniusDivision_primeRegular {ι : Type u}
    (hp : IsSMulRegular A (p : A))
    (e₀ : (A ⧸ Ideal.span {(p : A)}) ≃+* MvPolynomial ι (ZMod p)) :
    let B := DeltaAdjoinDivision E (p : A) (fun s => (E).frobeniusLift (x s))
    IsSMulRegular B (p : B) := by
  let B₀ := DeltaAdjoinDivision E (p : A) x
  let f := (E).frobeniusLift
  have hfδ : (E).IsDeltaHom E f := Prismatic.frobeniusLift_isDeltaHom_of_regular E hp
  let e : A ≃+* Prismatic.CrystallineFrobeniusTarget E := ULift.ringEquiv.symm
  let g := deltaAdjoinDivisionMap E (p : A) x
  let j := deltaAdjoinDivisionMap E (f (p : A)) (fun s => f (x s))
  let k := deltaAdjoinDivisionBaseChange E E f hfδ (p : A) x
  have h := deltaAdjoinDivisionBaseChange_isPushout E E f hfδ (p : A) x
  have h' : IsPushout (CommRingCat.ofHom (e.toRingHom.comp f)) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((j).comp e.symm.toRingHom)) (CommRingCat.ofHom k) := by
    refine h.of_iso (Iso.refl _) e.toCommRingCatIso (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · simp [g]
    · apply CommRingCat.hom_ext
      exact RingHom.ext fun t => congrArg j (e.symm_apply_apply t).symm
    · simp [k]
  have hB₀ : IsSMulRegular B₀ (p : B₀) := by
    intro a b hab
    let e₁ := freeCoordinatePDivisionEquiv D σ
    apply e₁.injective
    apply hp
    change (p : A) * e₁ a = (p : A) * e₁ b
    change (p : B₀) * a = (p : B₀) * b at hab
    simpa only [map_mul, map_natCast] using congrArg e₁ hab
  have hreg := Prismatic.crystallinePrimeRegular_of_isPushout p _ _ _ _ h'
    (Prismatic.crystallineCompletelyFlat_frobenius E hp e₀) hB₀
  change IsSMulRegular
    (DeltaAdjoinDivision E (f (p : A)) (fun s => f (x s))) _ at hreg
  rwa [map_natCast] at hreg

end PrimeRegular

section Factorial

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
  (D : DeltaStructure p A) (a : σ → A)

local notation "B" => DeltaAdjoinDivision D (p : A) (fun s => D.frobeniusLift (a s))

/-- 概要：p 正則な生の Frobenius 除算包と、p を反転した環内の階乗部分環の標準同型。
方針：既存の局所化像の計算と、p 正則性による局所化評価の単射性を組み合わせる。
規約：係数は p 局所（BS 著者版 Lemma 2.36、Corollary 2.39）。
使われ方：自由座標での分冪包との同定と、正則列への特殊化。 -/
def frobeniusDivisionFactorialEquiv (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hp : IsSMulRegular B (p : B)) : B ≃+* pDivisionFactorialSubring p a :=
  let f := deltaPDivisionToAway D (fun s => D.frobeniusLift (a s))
  let e : B ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => deltaPDivisionToAway_injective_of_p_mul_injective
      D (fun s => D.frobeniusLift (a s)) hp (congrArg Subtype.val h),
      f.rangeRestrict_surjective⟩
  e.trans (RingEquiv.subringCongr (pDivisionFactorialSubring_eq_raw_range hlocal D a).symm)

/-- 概要：階乗部分環への標準同型は係数上で局所化の標準射に一致する。
方針：局所化への δ 評価の係数上の式。
規約：BS 著者版 Lemma 2.36 の底の脚。
使われ方：押し出しによる正則列への特殊化。 -/
theorem frobeniusDivisionFactorialEquiv_base
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (hp : IsSMulRegular B (p : B)) (b : A) :
    frobeniusDivisionFactorialEquiv D a hlocal hp
        (deltaAdjoinDivisionMap D (p : A) (fun s => D.frobeniusLift (a s)) b) =
      pDivisionFactorialBase p a b := by
  apply Subtype.ext
  exact DFunLike.congr_fun (deltaPDivisionToAway_spec D (fun s => D.frobeniusLift (a s))).2.1 b

end Factorial

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 2.36"] _root_.SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivision_primeRegular
attribute [cite BS19 "Lemma 2.36"] _root_.SerrePositivity.BhattScholze.frobeniusDivisionFactorialEquiv
