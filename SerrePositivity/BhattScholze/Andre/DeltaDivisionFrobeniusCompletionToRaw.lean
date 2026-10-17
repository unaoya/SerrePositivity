module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFrobeniusCompletedResidue
public import SerrePositivity.BhattScholze.Andre.PDCompletionPairResidue

/-!
# André E1・E2：Frobenius 側の実完備化剰余を raw 剰余へ戻す

## 概要

完全 δ 環上の raw 包の実完備化後の (d,φ⁻¹(d)) 商は、
Frobenius 側の未完備 raw 包の (p,d) 商と環同型。
BS Rem 7.15（著者版 p.62）の実完備化後の剰余計算の一段。

## 方針

φ(d) が (p,d) に属すことを使い、実完備化側の二元剰余比較の後に
両完備化座標を殺す商の普遍性による同型を合成する。

## 規約

実 H⁰ と標準単位を保持し、raw 剰余と pd 包の同定はまだ含めない。

## 使われ方

完備化後の Frobenius 比較を、通常代数として計算する raw 剰余へ接続する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (a : σ → A)
local notation "φ" => D.frobeniusLift
local notation "e" => DeltaStructure.frobeniusEquiv D hD
local notation "x" => RingEquiv.symm (DeltaStructure.frobeniusEquiv D hD) d
local notation "L" => DeltaAdjoinDivision D d a
local notation "M" => DeltaAdjoinDivision D (e d) (fun s => e (a s))
local notation "jL" => deltaAdjoinDivisionMap D d a
local notation "jM" => deltaAdjoinDivisionMap D (e d) (fun s => e (a s))
local notation "HL" => PDCompletionH0 L p (jL d)
local notation "uL" => pdCompletionUnit L p (jL d)

/-- 概要：Frobenius 側の実完備化の第二座標は raw 包の (p,d) イデアルに属す。
方針：φ(d)=d^p+pδ(d) の各項の所属を係数射で送る。
規約：d の distinguished 性はこの所属計算には不要。
使われ方：BS Rem 7.15（著者版 p.62）の完備化座標を殺す商比較への入力。 -/
theorem deltaDivisionFrobeniusCompletionCoordinate_mem :
    jM (e d) ∈ Ideal.span {(p : M), jM d} := by
  have hd : d ∈ Ideal.span {(p : A), d} := Ideal.subset_span (by simp)
  have hp : (p : A) ∈ Ideal.span {(p : A), d} := Ideal.subset_span (by simp)
  have hφ : φ d ∈ Ideal.span {(p : A), d} := by
    rw [D.frobeniusLift_apply]
    exact (Ideal.span {(p : A), d}).add_mem
      ((Ideal.span {(p : A), d}).pow_mem_of_mem hd p (Nat.Prime.pos (Fact.out : p.Prime)))
      ((Ideal.span {(p : A), d}).mul_mem_right _ hp)
  have h := Ideal.mem_map_of_mem jM hφ
  change jM (D.frobeniusLift d) ∈ Ideal.span {(p : M), jM d}
  simpa only [Ideal.map_span, Set.image_pair, map_natCast] using h

/-- 概要：元の raw 包の実完備化後の剰余は Frobenius 側の未完備 raw 剰余と環同型。
方針：実完備化後の Frobenius 同型と、両座標を殺す二元商の比較を合成する。
規約：係数 δ 環は完全、d は distinguished とする。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包へ進む未完備剰余への接続。 -/
def deltaDivisionFrobeniusCompletionToRawEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing L p (jL d)
    (HL ⧸ Ideal.span {uL (jL d), uL (jL x)}) ≃+*
      (M ⧸ Ideal.span {(p : M), jM d}) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  exact (deltaDivisionFrobeniusCompletedResidueEquiv D hD d a hd).trans
    (pdCompletionPairResidueEquiv p (jM (e d)) (jM d)
      (deltaDivisionFrobeniusCompletionCoordinate_mem D hD d a))

/-- 概要：実完備化から raw 剰余への比較は係数 b を φ(b) の剰余へ送る。
方針：完備化後の Frobenius 係数公式と二元剰余比較の単位公式を使う。
規約：元の係数射と実完備化単位を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包へ接続する係数作用。 -/
theorem deltaDivisionFrobeniusCompletionToRawEquiv_coeff
    (hd : D.IsDistinguished d) (b : A) :
    letI := pdCompletionCommRing L p (jL d)
    deltaDivisionFrobeniusCompletionToRawEquiv D hD d a hd
      (Ideal.Quotient.mk _ (uL (jL b))) = Ideal.Quotient.mk _ (jM (φ b)) := by
  let := pdCompletionCommRing L p (jL d)
  let := pdCompletionCommRing M p (jM (e d))
  rw [deltaDivisionFrobeniusCompletionToRawEquiv, RingEquiv.trans_apply,
    deltaDivisionFrobeniusCompletedResidueEquiv_coeff, pdCompletionPairResidueEquiv_unit]

end SerrePositivity.BhattScholze.Andre
