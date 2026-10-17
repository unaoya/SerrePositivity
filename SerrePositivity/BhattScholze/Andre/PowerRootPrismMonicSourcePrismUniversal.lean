module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicRegularSource
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicOriginalInputSquare

/-!
# André A1-a：正則性を明示した源 prism の入力作用を保つ普遍性

## 概要

H の生成元正則性と H/d の p 完備性を明示すると、原典の完備入力作用を保つ
H の prism から有界試験 prism への射は一意に存在する。BS Rem 7.15（著者版 p.62）。

## 方針

基底を保つ δ 射をイデアル保存性で prism 射にまとめる。
剰余射と既存の標準入力作用を照合して、環射の一意性を prism 射の一意性へ移す。
原典を補う元の実完備化と明示的な可換図式による経路。

## 規約

hreg と hT は解消せず、源の無条件の prism 性や絶対 envelope 全体の完成とは数えない。
既存の hpR 付き定理は変更しない。

## 使われ方

並列の正則性・完備性の成果が到着したときに、元の源 prism の普遍性へ合流する。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
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

variable {B : Type u} [CommRing B] (Q : OrientedPrism p B)
variable (k : OrientedPrism.Hom W Q)
local notation "qB" => Ideal.Quotient.mk Q.ideal
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f
local notation "φ₀" => powerRootPrismMonicHodgeTateBaseMap W hW f
/-- 概要：基底を保つ H の δ 射は条件付き源 prism からの prism 射になる。
方針：分母の像が基底 prism 射の生成元像となることからイデアル保存性を得る。
規約：元の環射と δ 構造を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の δ 普遍性から prism 普遍性への移送。 -/
def powerRootPrismMonicSourceHomOfDelta :
    let := pdCompletionCommRing L p (jL dP)
    (hreg : IsSMulRegular H (uL (jL dP))) →
    (F : H →+* B) → (DH).IsDeltaHom Q.deltaStructure F → F.comp baseH = k.toRingHom →
      OrientedPrism.Hom (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg F hδ hF
  refine ⟨F, hδ, ?_⟩
  change Ideal.span {uL (jL dP)} ≤ Q.ideal.comap F
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = uL (jL dP) := Set.mem_singleton_iff.mp hx
  rw [hxd]
  change F (baseH W.generator) ∈ Q.ideal
  rw [show F (baseH W.generator) = k.toRingHom W.generator from
    RingHom.congr_fun hF W.generator]
  exact k.map_generator_mem

/-- 概要：構成した源 prism 射の台の環射は元の F。
方針：構成の定義を使う。
規約：標準射の値を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の環射の一意性の移送。 -/
theorem powerRootPrismMonicSourceHomOfDelta_toRingHom :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP))) (F : H →+* B)
      (hδ : (DH).IsDeltaHom Q.deltaStructure F) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicSourceHomOfDelta W hW f Q k hreg F hδ hF).toRingHom = F := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg F hδ hF
  rfl

/-- 概要：構成した源 prism 射は元の基底 prism 射と可換。
方針：台の環射の合成等式を prism 射の外延性で戻す。
規約：同じ標準基底射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の基底上の prism 射。 -/
theorem powerRootPrismMonicSourceHomOfDelta_comp_base :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP))) (F : H →+* B)
      (hδ : (DH).IsDeltaHom Q.deltaStructure F) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicSourceHomOfDelta W hW f Q k hreg F hδ hF).comp
        (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg) = k := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg F hδ hF
  exact OrientedPrism.Hom.ext hF

/-- 概要：条件付き源 prism の商射は既存の H/d の剰余射と一致する。
方針：H の代表元上で二つの主商の射を比較する。
規約：任意の基底保存 prism 射について成り立つ。
使われ方：BS Rem 7.15（著者版 p.62）の完備入力図式を prism 射で表す。 -/
theorem powerRootPrismMonicSourceHom_quotientMap :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (G : OrientedPrism.Hom (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q)
      (hG : G.toRingHom.comp baseH = k.toRingHom),
      G.quotientMap = powerRootPrismMonicReductionMap W hW f Q k G.toRingHom hG := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg G hG
  apply Ideal.Quotient.ringHom_ext
  rfl

set_option maxHeartbeats 800000 in
-- 元の H⁰ の prism 構造と完備入力作用を保持して一意存在を移すため。
/-- 概要：原典の完備入力作用を保つ条件付き源 prism からの射は一意に存在。
方針：入力作用を保つ一意な δ 射を prism 射にまとめ、台の環射による外延性を使う。
規約：hreg と hT の解消は別工程。条件付き成果を最終同定とは数えない。
使われ方：BS Rem 7.15（著者版 p.62）の絶対 prismatic envelope の合流点。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_preserving_original_input
    (hf : f.Monic)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (hT : IsAdicComplete (Ideal.span {(p : T)}) T),
    ∃! G : OrientedPrism.Hom (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q,
      G.comp (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg) = k ∧
        G.quotientMap.comp (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hT
  obtain ⟨F, ⟨hFδ, hF, hs⟩, hu⟩ :=
    existsUnique_powerRootPrismMonicHom_preserving_original_input W hW f Q k hf hB η hη hT
  let G := powerRootPrismMonicSourceHomOfDelta W hW f Q k hreg F hFδ hF
  refine ⟨G, ⟨powerRootPrismMonicSourceHomOfDelta_comp_base W hW f Q k hreg F hFδ hF, ?_⟩, ?_⟩
  · rw [powerRootPrismMonicSourceHom_quotientMap W hW f Q k hreg G hF]
    exact hs
  · intro K hK
    have hKb : K.toRingHom.comp baseH = k.toRingHom :=
      congrArg OrientedPrism.Hom.toRingHom hK.1
    have hKs : (powerRootPrismMonicReductionMap W hW f Q k K.toRingHom hKb).comp
        (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η := by
      rw [← powerRootPrismMonicSourceHom_quotientMap W hW f Q k hreg K hKb]
      exact hK.2
    apply OrientedPrism.Hom.ext
    exact hu K.toRingHom ⟨K.map_delta, hKb, hKs⟩

/-- 概要：H/d の有界 p ねじれから通常の p 完備性を得る。
方針：実完備化の導来 p 完備性を主商へ移し、有界ねじれ比較を使う。
規約：生成元正則性や hpR は使わず、有界ねじれを明示引数とする。
使われ方：BS Rem 7.15（著者版 p.62）の有界源から完備入力作用への接続。 -/
theorem powerRootPrismMonicSourceQuotient_complete_of_bounded :
    let := pdCompletionCommRing L p (jL dP)
    (∃ N : ℕ, ∀ n : ℕ, ∀ x : T, (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0) →
      IsAdicComplete (Ideal.span {(p : T)}) T := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hBound
  apply (isRingModuleComplete_iff_isAdicComplete_natCast_of_bounded_torsion T p hBound).mp
  exact isModuleComplete_principal_quotient_natCast H p (uL (jL dP))
    (pdCompletionH0_self_complete_p L p (jL dP))

set_option maxHeartbeats 800000 in
-- 有界ねじれ比較から得た完備性を元の源 prism の依存型のまま供給するため。
/-- 概要：源の生成元正則性と剰余の有界 p ねじれから、入力作用を保つ prism 射は一意。
方針：有界ねじれから通常の p 完備性を内部で供給し、証明済みの prism 普遍性を使う。
規約：hreg と有界ねじれの証明は明示仮定に残す。
使われ方：BS Rem 7.15（著者版 p.62）の有界源の絶対 envelope への合流点。 -/
theorem existsUnique_powerRootPrismMonicPrismHom_of_bounded_source
    (hf : f.Monic)
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
        (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0),
    let hT := powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f hBound
    ∃! G : OrientedPrism.Hom (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) Q,
      G.comp (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg) = k ∧
        G.quotientMap.comp (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound
  exact existsUnique_powerRootPrismMonicPrismHom_preserving_original_input
    W hW f Q k hf hB η hη hreg
      (powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f hBound)

end SerrePositivity.BhattScholze.Andre
