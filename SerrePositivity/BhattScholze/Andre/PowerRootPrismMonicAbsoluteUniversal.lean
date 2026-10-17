module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicSourceInitiality
public import SerrePositivity.BhattScholze.Andre.PerfectPrismBoundedTargetLift

/-!
# André A1-a：基底射を指定しない有界入力への源の普遍性

## 概要

元の正次数モニック源は、完備入力作用だけを持つ任意の有界な向き付き prism へ一意に写る。
BS Rem 7.15（著者版 p.62）の絶対 envelope の普遍性の向き付き対象での形。

## 方針

入力作用の係数制限から、Lemma 4.8（著者版 pp.38–39）の証明済みの持上げで基底射を作る。
固定基底上での源の普遍性を適用し、完全基底からの剛性で任意の入力保存射の基底保存性を回復する。
原典の変形理論とは異なる tilt 比較・Fontaine 写像・実完備化による経路。

## 規約

標的の完全性・p 正則性や基底射の選択は引数に残さない。源の hreg・hBound も要求しない。
向き付き prism を扱い、一般 Cartier イデアルを持つ対象との比較は別工程。

## 使われ方

原典の順序の完備入力環 S の作用だけを与えた場合の、同じ H の初期性の判定。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable {B : Type u} [CommRing B]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f



local notation "DL" => deltaAdjoinDivisionStructure E dP a
local notation "DH" => deltaPDCompletionStructure DL (jL dP)


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "jS" => algebraMap S₀ CS
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})

open CategoryTheory CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

variable (hdeg : 0 < f.natDegree)

set_option maxHeartbeats 800000 in
-- 元の H の環構造・標準入力・持上げた基底射を同時に照合するため。
/-- 概要：完備入力作用だけを持つ任意の有界 prism への源からの射は一意に存在。
方針：完全基底の商射を一意に持ち上げ、固定基底の普遍性と基底射の剛性を使う。
規約：源の正則性・有界性、標的の基底射を仮定に残さず、入力圏と同じ宇宙で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の絶対 envelope の向き付き対象での普遍性。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_of_absolute_input
    (Q : OrientedPrism p B)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal) :
    let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
    ∃! G : OrientedPrism.Hom X.prism Q, G.quotientMap.comp X.input = η := by
  let X := powerRootPrismMonicSourceInputObjectOfMonicPositive W hW f hf hdeg
  obtain ⟨k, hk, _⟩ := existsUnique_perfectPrismHomLift_to_bounded W hW Q hB (η.comp cS)
  let := pdCompletionCommRing L p (jL dP)
  have hreg := powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional
    W hW f hf hdeg
  have hBound := powerRootPrismMonicHodgeTate_bounded_prime_torsion_of_unconditional
    W hW f hf hdeg
  obtain ⟨G, hG, hu⟩ := existsUnique_powerRootPrismMonicPrismHom_of_bounded_source
    W hW f Q k hf hB η hk.symm hreg hBound
  refine ⟨G, hG.2, ?_⟩
  intro G' hG'
  have hb : G'.comp X.base = k := by
    apply perfectPrismHom_ext_to_bounded_target W hW Q hB
    rw [OrientedPrism.Hom.quotientMap_comp, ← X.input_base,
      ← RingHom.comp_assoc, hG', hk]
  exact hu G' ⟨hb, hG'⟩

end SerrePositivity.BhattScholze.Andre
