module

public import SerrePositivity.BhattScholze.Andre.BoundedPrismInputCategory
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicSourcePrismUniversal

/-!
# André A1-a：元の H の入力作用を持つ対象と初期性

## 概要

生成元正則性と H/d の有界 p ねじれが供給されたとき、元の H を原典の完備入力作用を持つ
有界 prism の対象とし、その圏で初期であることを証明する。
BS Rem 7.15（著者版 p.62）の envelope 比較の合流点。

## 方針

同じ H の prism 構造・標準基底射・標準完備入力射を対象にまとめる。
証明済みの基底と入力作用を保つ prism 射の一意存在から IsInitial を構成する。
原典を補う明示的な圏と元の raw 実完備化による経路。

## 規約

正則性 hreg と有界ねじれ hBound は明示引数のまま保持する。
これらの無条件の供給や、絶対 envelope 全体の同定完了とは数えない。
固定基底 W・向き付き対象の圏と原典の絶対 prismatic site との比較も別工程。

## 使われ方

並列成果が到着したときに、元の H の初期性と任意の envelope との同型を合流する。
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

open CategoryTheory CategoryTheory.Limits
local notation "cS" => RingHom.comp lS (algebraMap R PR)
variable (hf : f.Monic)

set_option maxHeartbeats 800000 in
-- 元の H の環構造と完備入力の係数作用を、対象の各構造と照合するため。
/-- 概要：正則性と有界ねじれが供給されると元の H を有界入力 prism の対象にまとめる。
方針：同じ台環・生成元・基底射・標準入力射とその可換性を束ねる。
規約：hreg と hBound は証明済みとみなさず明示引数とする。
使われ方：BS Rem 7.15（著者版 p.62）の源の初期性を述べる対象。 -/
def powerRootPrismMonicSourceInputObject :
    let := pdCompletionCommRing L p (jL dP)
    (hreg : IsSMulRegular H (uL (jL dP))) →
    (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
      (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0) → BoundedPrismInput W cS := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound
  let hT := powerRootPrismMonicSourceQuotient_complete_of_bounded W hW f hBound
  refine
    { ring := CommRingCat.of H
      prism := powerRootPrismMonicCompletionPrismOfRegular W hW f hreg
      base := powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg
      input := powerRootPrismMonicOriginalInputMap W hW f hf hT
      input_base := ?_
      bounded := hBound }
  calc
    _ = powerRootPrismMonicHodgeTateBaseMap W hW f :=
      powerRootPrismMonicOriginalInputMap_coeff W hW f hf hT
    _ = _ := by
      apply Ideal.Quotient.ringHom_ext
      rfl

set_option maxHeartbeats 800000 in
-- 初期性の対象の依存する環構造と元の H の普遍性を同時に照合するため。
/-- 概要：明示した正則性と有界ねじれの下で元の H の入力 prism 対象は初期。
方針：任意の有界入力 prism への射の一意存在を既存の普遍性から供給する。
規約：hreg と hBound の無条件の解消は別工程。
使われ方：BS Rem 7.15（著者版 p.62）の envelope の初期性への条件付き接続。 -/
def powerRootPrismMonicSourceInput_isInitial :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
        (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0),
      IsInitial (powerRootPrismMonicSourceInputObject W hW f hf hreg hBound) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound
  apply BoundedPrismInput.isInitialOfPrismUniversal
  intro Y
  exact existsUnique_powerRootPrismMonicPrismHom_of_bounded_source
    W hW f Y.prism Y.base hf Y.bounded Y.input Y.input_base hreg hBound

set_option maxHeartbeats 800000 in
-- 元の H の初期対象と任意の初期対象の依存型を保持して同型を作るため。
/-- 概要：元の H の条件付き初期対象は、同じ入力圏の任意の初期対象と同型。
方針：二つの初期対象の一意な同型を使う。
規約：比較先の初期性も明示引数として要求する。
使われ方：BS Rem 7.15（著者版 p.62）の原典の普遍性との条件付き同定。 -/
def powerRootPrismMonicSourceInputIso :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
        (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0)
      (Z : BoundedPrismInput W cS),
      IsInitial Z → (powerRootPrismMonicSourceInputObject W hW f hf hreg hBound ≅ Z) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound Z hZ
  exact (powerRootPrismMonicSourceInput_isInitial W hW f hf hreg hBound).uniqueUpToIso hZ

set_option maxHeartbeats 800000 in
-- 初期対象の同型から元の H と比較対象の台環の同型を取り出すため。
/-- 概要：同じ入力圏の任意の初期対象と元の H の台環は条件付きで環同型。
方針：初期対象の一意な同型から台環の環同型を取り出す。
規約：hreg、hBound、比較先の初期性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の元の H と envelope の実環としての比較。 -/
def powerRootPrismMonicSourceEnvelopeRingEquiv :
    let := pdCompletionCommRing L p (jL dP)
    IsSMulRegular H (uL (jL dP)) →
    (∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
      (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0) →
    ∀ Z : BoundedPrismInput W cS,
      IsInitial Z → (H ≃+* Z.ring) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound Z hZ
  exact BoundedPrismInput.isoRingEquiv
    (powerRootPrismMonicSourceInputIso W hW f hf hreg hBound Z hZ)

set_option maxHeartbeats 800000 in
-- 同型の基底保存性を元の H の標準係数射の各元へ戻すため。
/-- 概要：初期対象との環同型は元の A の全ての係数像を保つ。
方針：同型の prism 射の基底保存条件を各係数元に適用する。
規約：元の H の標準係数射を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の比較同型の係数作用の確認。 -/
theorem powerRootPrismMonicSourceEnvelopeRingEquiv_base_coeff (a₀ : A) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hreg : IsSMulRegular H (uL (jL dP)))
      (hBound : ∃ N : ℕ, ∀ n : ℕ, ∀ x : T,
        (p : T) ^ n * x = 0 → (p : T) ^ N * x = 0)
      (Z : BoundedPrismInput W cS) (hZ : IsInitial Z),
      powerRootPrismMonicSourceEnvelopeRingEquiv W hW f hf hreg hBound Z hZ
        (powerRootPrismMonicCompletionBaseMap W hW f a₀) = Z.base.toRingHom a₀ := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg hBound Z hZ
  let e := powerRootPrismMonicSourceInputIso W hW f hf hreg hBound Z hZ
  exact RingHom.congr_fun (congrArg OrientedPrism.Hom.toRingHom e.hom.over_base) a₀

end SerrePositivity.BhattScholze.Andre
