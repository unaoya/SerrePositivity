module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicStandardEquationInput
public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicEquationInput

/-!
# André A1-a：標準入力射を保つ実完備化の普遍性

## 概要

基底を保つ H の環射は H/d から試験 prism の商への射を誘導する。
通常の入力射の可換性は全根の保存と同値であり、それを保つ δ 射は一意に存在する。
BS Rem 7.15（著者版 p.62）の入力作用を含む比較への接続。

## 方針

基底射の生成元像で剰余射を構成し、係数と全根による方程式商の外延性を使う。
原典を補う通常の主商と明示的な可換図式による経路。

## 規約

源 H の prism 性・通常入力の完備化はこの段階で前提としない。
モニック性・正次数・prism 商の p 正則性は不要。

## 使われ方

根の等式で記述した普遍性を、標準入力作用を保つ射の一意性へ移す。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}


local notation "fR" => f.map (Ideal.Quotient.mk W.ideal)
local notation "S₀" => PowerRootEquationQuotient p hp fR
local notation "φ₀" => powerRootPrismMonicHodgeTateBaseMap W hW f

variable {B : Type u} [CommRing B] (Q : OrientedPrism p B)
variable (k : OrientedPrism.Hom W Q)
local notation "qB" => Ideal.Quotient.mk Q.ideal
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "input₀" => powerRootPrismMonicEquationInputMap W hW f
local notation "cS" => powerRootEquationQuotientCoeff p hp fR
local notation "rS" => powerRootEquationQuotientRoot p hp fR
local notation "DH" => deltaPDCompletionStructure (deltaAdjoinDivisionStructure E dP a) (jL dP)

/-- 概要：基底を保つ H の環射は H/d から試験 prism の商への射を誘導する。
方針：分母の像が基底 prism 射の生成元像となることを使って主商へ降下する。
規約：射自体の δ 保存性はこの剰余射の定義には不要。
使われ方：BS Rem 7.15（著者版 p.62）の入力図式の右側の剰余射。 -/
def powerRootPrismMonicReductionMap :
    let := pdCompletionCommRing L p (jL dP)
    (F : H →+* B) → F.comp baseH = k.toRingHom → T →+* B ⧸ Q.ideal := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF
  apply Ideal.Quotient.lift (Ideal.span {dH}) ((qB).comp F)
  change Ideal.span {dH} ≤ RingHom.ker ((qB).comp F)
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = dH := Set.mem_singleton_iff.mp hx
  rw [hxd]
  change qB (F (baseH W.generator)) = 0
  rw [show F (baseH W.generator) = k.toRingHom W.generator from
    RingHom.congr_fun hF W.generator]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr k.map_generator_mem

/-- 概要：誘導剰余射は H の代表元に元の射を適用する。
方針：主商への降下の定義を使う。
規約：任意の H の元について成り立つ。
使われ方：BS Rem 7.15（著者版 p.62）の全標準根の像の比較。 -/
theorem powerRootPrismMonicReductionMap_mk :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (F : H →+* B) (hF : F.comp baseH = k.toRingHom) (x : H),
      powerRootPrismMonicReductionMap W hW f Q k F hF (qH x) = qB (F x) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF x
  rfl

/-- 概要：誘導剰余射は元の prism 商からの基底射と可換。
方針：元の基底 A の代表元で環射の合成等式を確認する。
規約：自然な商係数作用を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の基底上の入力作用の保存。 -/
theorem powerRootPrismMonicReductionMap_coeff :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (F : H →+* B) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicReductionMap W hW f Q k F hF).comp φ₀ = k.quotientMap := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  change qB (F (baseH x)) = qB (k.toRingHom x)
  exact congrArg qB (RingHom.congr_fun hF x)

/-- 概要：通常の入力図式の可換性は全ての標準根の保存と同値。
方針：係数の可換性を基底保存性で供給し、方程式商の外延性で全根から全元へ移す。
規約：基底を保つ任意の環射について成立する。
使われ方：BS Rem 7.15（著者版 p.62）の入力作用を含む普遍性への変換。 -/
theorem powerRootPrismMonicEquationInputSquare_iff_roots
    (η : S₀ →+* B ⧸ Q.ideal) (hη : η.comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (F : H →+* B) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicReductionMap W hW f Q k F hF).comp input₀ = η ↔
        ∀ n, qB (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = η (rS n) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF
  constructor
  · intro hs n
    have h := RingHom.congr_fun hs (rS n)
    rw [RingHom.comp_apply, powerRootPrismMonicEquationInputMap_root] at h
    exact h
  · intro hr
    apply powerRootEquationQuotient_ringHom_ext p hp fR
    · rw [RingHom.comp_assoc, powerRootPrismMonicEquationInputMap_coeff,
        powerRootPrismMonicReductionMap_coeff, hη]
    · intro n
      change powerRootPrismMonicReductionMap W hW f Q k F hF (input₀ (rS n)) = η (rS n)
      rw [powerRootPrismMonicEquationInputMap_root]
      exact hr n

/-- 概要：通常の標準入力射を保つ H から有界試験 prism への δ 射は一意に存在。
方針：根列の普遍性と入力図式の可換性との同値を使う。
規約：H 自体の prism 性はこの段階で主張しない。
使われ方：BS Rem 7.15（著者版 p.62）の入力作用を含む絶対 envelope 比較。 -/
theorem existsUnique_powerRootPrismMonicHom_preserving_equation_input
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : S₀ →+* B ⧸ Q.ideal) (hη : η.comp cS = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B, (DH).IsDeltaHom Q.deltaStructure F ∧
      ∃ hF : F.comp baseH = k.toRingHom,
        (powerRootPrismMonicReductionMap W hW f Q k F hF).comp input₀ = η := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  obtain ⟨F, hF, hu⟩ := existsUnique_powerRootPrismMonicCompletionHom_of_equation_input
    W hW f Q hB k η hη
  refine ⟨F, ⟨hF.1, ⟨hF.2.1, ?_⟩⟩, ?_⟩
  · exact (powerRootPrismMonicEquationInputSquare_iff_roots W hW f Q k η hη F hF.2.1).mpr
      (hF.2.2)
  · rintro K ⟨hKδ, hK, hs⟩
    exact hu K ⟨hKδ, hK,
      (powerRootPrismMonicEquationInputSquare_iff_roots W hW f Q k η hη K hK).mp hs⟩

end SerrePositivity.BhattScholze.Andre
