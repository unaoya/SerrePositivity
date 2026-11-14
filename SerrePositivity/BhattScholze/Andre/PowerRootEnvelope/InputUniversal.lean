module

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputCategory

/-!
# 入力射を保つ普遍性と envelope の初期性

## 概要
完全試験 prism の剰余根データによる普遍性、方程式入力・完備入力から H/d への標準射とそれを保つ普遍性、源 prism の入力作用を保つ普遍性、入力作用を持つ対象の圏での初期性（原典の Δ_S が envelope であること）。
BS 著者版 Proposition 3.13 の普遍性を、Remark 7.15 のモニック根の入力で扱う。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`PowerRootEnvelope/Initiality`、`PowerRootEnvelope/Unconditional/FrobeniusPD`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## André A1-a：通常の入力環から H/d への標準射

## 概要

通常の方程式商 (A/d)[Y^(1/p^∞)]/(f) を、元の実完備化の分母商 H/d へ送る。
全根変数と係数を自然な標準像へ写す。BS 著者版 Remark 7.15（著者版 p.62）の入力作用。

## 方針

元の無限根変数の像は互換根列をなし、raw 関係により第零根が f を消す。
通常の方程式商の普遍性で標準射を構成する。原典を補う具体的な入力射による経路。

## 規約

モニック性・正次数・prism 商の p 正則性を仮定しない。完備入力への延長は別工程。

## 使われ方

試験射の入力作用の保存を、個々の根の等式から環射の可換性へ移す。
-/

@[expose] public noncomputable section PowerRootPrismMonicStandardEquationInput

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

/-- 概要：H/d 内の全ての標準無限根変数の像。
方針：元の根変数を raw 包・実完備化・分母商へ順に写す。
規約：全ての段 n を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力の標準根列。 -/
def powerRootPrismMonicHodgeTateRoots (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    T := by
  let := pdCompletionCommRing L p (jL dP)
  exact qH (uL (jL (powerRootPolynomialVariable A p hp n)))

/-- 概要：H/d の標準根列は p 冪に関して互換。
方針：無限根環の関係式を三つの標準環射で写す。
規約：正則性の追加仮定は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力環の標準作用。 -/
theorem powerRootPrismMonicHodgeTateRoots_pow (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicHodgeTateRoots W hW f (n + 1) ^ p =
      powerRootPrismMonicHodgeTateRoots W hW f n := by
  let := pdCompletionCommRing L p (jL dP)
  exact (map_pow ((qH).comp ((uL).comp jL)) _ _).symm.trans
    (congrArg ((qH).comp ((uL).comp jL)) (powerRootPolynomialVariable_pow A p hp n))

/-- 概要：標準根列の第零根は元の入力多項式の係数商像を消す。
方針：既存の raw 関係による第零根の評価定理を使う。
規約：モニック性・正次数・p 正則性を要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の方程式商の降下条件。 -/
theorem powerRootPrismMonicHodgeTateRoots_eval :
    let := pdCompletionCommRing L p (jL dP)
    (fR).eval₂ φ₀ (powerRootPrismMonicHodgeTateRoots W hW f 0) = 0 :=
  powerRootPrismMonicHodgeTateRoot_eval W hW f

/-- 概要：通常の方程式商から元の H/d への標準入力射。
方針：自然な係数射と標準互換根列を方程式商の普遍性に渡す。
規約：標的の通常の p 完備性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の未完備入力作用。 -/
def powerRootPrismMonicEquationInputMap :
    let := pdCompletionCommRing L p (jL dP)
    S₀ →+* T := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose

/-- 概要：標準入力射は係数射と可換。
方針：方程式商の一意存在の係数条件を取り出す。
規約：元の prism 商 R の自然な作用を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底を保つ入力作用。 -/
theorem powerRootPrismMonicEquationInputMap_coeff :
    let := pdCompletionCommRing L p (jL dP)
    (powerRootPrismMonicEquationInputMap W hW f).comp
      (powerRootEquationQuotientCoeff p hp fR) = φ₀ := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose_spec.1.1

/-- 概要：標準入力射は全ての入力根を元の H/d の標準像へ送る。
方針：方程式商の一意存在の根条件を取り出す。
規約：全ての段 n に対する実際の入力像を保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力射と試験射の可換性。 -/
theorem powerRootPrismMonicEquationInputMap_root (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    powerRootPrismMonicEquationInputMap W hW f (powerRootEquationQuotientRoot p hp fR n) =
      powerRootPrismMonicHodgeTateRoots W hW f n := by
  let := pdCompletionCommRing L p (jL dP)
  exact (existsUnique_powerRootEquationQuotientHom p hp fR φ₀
    (powerRootPrismMonicHodgeTateRoots W hW f)
    (powerRootPrismMonicHodgeTateRoots_pow W hW f)
    (powerRootPrismMonicHodgeTateRoots_eval W hW f)).choose_spec.1.2 n

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicStandardEquationInput

/-! ## André A1-a：完備入力環から H/d への標準射の接続

## 概要

H/d の通常の p 完備性を明示仮定にすると、原典の順序の完備入力環から H/d への
係数と全根を保つ標準射を構成できる。BS 著者版 Remark 7.15（著者版 p.62）の入力作用。

## 方針

通常の入力射を p 完備化から一意に延長し、モニック入力の商と完備化の交換同型を合成する。
原典を補う主商と完備化の明示的な普遍性による経路。

## 規約

H/d の p 完備性はこのファイルで証明せず明示引数にする。hpR で代用しない。
源 H の prism 性と絶対 envelope 全体の同定は別工程。

## 使われ方

並列成果から通常の p 完備性が供給された時点で、原典の完備入力作用を接続する。
-/

@[expose] public noncomputable section PowerRootPrismMonicStandardCompletedInput

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

local notation "PR" => PowerRootPolynomial R p hp
local notation "CR" => AdicCompletion (Ideal.span {(p : PR)}) PR
local notation "zR" => powerRootPolynomialBaseMap R p hp fR
local notation "SI" => PowerRootMonicCompletedInput p hp fR
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap PR CR zR})) (algebraMap PR CR)
local notation "CS" => AdicCompletion (Ideal.span {(p : S₀)}) S₀
local notation "qR" => Ideal.Quotient.mk (Ideal.span {zR})
local notation "input₀" => powerRootPrismMonicEquationInputMap W hW f
variable (hf : f.Monic)

/-- 概要：H/d の通常の p 完備性から、原典の完備入力環の標準作用を構成する。
方針：通常の入力射を完備化へ延長し、モニック交換同型と合成する。
規約：hT は証明済みとみなさず明示引数のまま保持する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の S→H/d の条件付き接続点。 -/
def powerRootPrismMonicOriginalInputMap :
    let := pdCompletionCommRing L p (jL dP)
    (hT : IsAdicComplete (Ideal.span {(p : T)}) T) → SI →+* T := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  let : IsAdicComplete (Ideal.span {(p : T)}) T := hT
  exact ((existsUnique_primeAdicCompletionHom S₀ p input₀).choose).comp
    (powerRootMonicCompletedInputEquiv p hp fR (hf.map (Ideal.Quotient.mk W.ideal))).toRingHom

/-- 概要：完備入力の標準作用は元の無限根多項式の像を通常の入力射へ戻す。
方針：交換同型の係数公式と完備化の延長条件を使う。
規約：元の無限根多項式の全ての元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力作用の根・係数の追跡。 -/
theorem powerRootPrismMonicOriginalInputMap_poly (x : PR) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
    powerRootPrismMonicOriginalInputMap W hW f hf hT (lS x) = input₀ (qR x) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  let : IsAdicComplete (Ideal.span {(p : T)}) T := hT
  change (existsUnique_primeAdicCompletionHom S₀ p input₀).choose
    (powerRootMonicCompletedInputEquiv p hp fR (hf.map (Ideal.Quotient.mk W.ideal)) (lS x)) = _
  exact (congrArg (existsUnique_primeAdicCompletionHom S₀ p input₀).choose
    (powerRootMonicCompletedInputEquiv_coeff p hp fR
      (hf.map (Ideal.Quotient.mk W.ideal)) x)).trans
        (RingHom.congr_fun (existsUnique_primeAdicCompletionHom S₀ p input₀).choose_spec.1 (qR x))

/-- 概要：原典の完備入力環からの標準射は元の R 係数射と可換。
方針：多項式入力公式と通常の入力射の係数公式を合成する。
規約：自然な係数作用を変更しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底上の完備入力図式。 -/
theorem powerRootPrismMonicOriginalInputMap_coeff :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
    (powerRootPrismMonicOriginalInputMap W hW f hf hT).comp
      ((lS).comp (algebraMap R PR)) = φ₀ := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  apply RingHom.ext
  intro x
  change powerRootPrismMonicOriginalInputMap W hW f hf hT (lS (algebraMap R PR x)) = φ₀ x
  rw [powerRootPrismMonicOriginalInputMap_poly W hW f hf _ hT]
  exact RingHom.congr_fun (powerRootPrismMonicEquationInputMap_coeff W hW f) x

/-- 概要：原典の完備入力環の全根は H/d の元の標準根へ写る。
方針：多項式入力公式を各根変数に適用し、通常の入力射の根公式を使う。
規約：全ての段 n を保持し、hT の解消は別工程。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力図式を全根で確認する。 -/
theorem powerRootPrismMonicOriginalInputMap_root (n : ℕ) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
    powerRootPrismMonicOriginalInputMap W hW f hf hT (lS (powerRootPolynomialVariable R p hp n)) =
      powerRootPrismMonicHodgeTateRoots W hW f n := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  exact (powerRootPrismMonicOriginalInputMap_poly W hW f hf _ hT).trans
    (powerRootPrismMonicEquationInputMap_root W hW f n)

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicStandardCompletedInput

/-! ## André A1-a：標準入力射を保つ実完備化の普遍性

## 概要

基底を保つ H の環射は H/d から試験 prism の商への射を誘導する。
通常の入力射の可換性は全根の保存と同値であり、それを保つ δ 射は一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の入力作用を含む比較への接続。

## 方針

基底射の生成元像で剰余射を構成し、係数と全根による方程式商の外延性を使う。
原典を補う通常の主商と明示的な可換図式による経路。

## 規約

源 H の prism 性・通常入力の完備化はこの段階で前提としない。
モニック性・正次数・prism 商の p 正則性は不要。

## 使われ方

根の等式で記述した普遍性を、標準入力作用を保つ射の一意性へ移す。
-/

@[expose] public noncomputable section PowerRootPrismMonicEquationInputSquare

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力図式の右側の剰余射。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全標準根の像の比較。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底上の入力作用の保存。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力作用を含む普遍性への変換。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の入力作用を含む絶対 envelope 比較。 -/
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

end PowerRootPrismMonicEquationInputSquare

/-! ## André A1-a：原典の完備入力作用を保つ実完備化の普遍性

## 概要

H/d の通常の p 完備性の明示仮定の下で、原典の完備入力環の標準作用を保つ
H から有界試験 prism への δ 射は一意に存在する。BS 著者版 Remark 7.15（著者版 p.62）の比較。

## 方針

完備な標的への入力射の外延性を使い、全根の保存から入力環全体の可換性を得る。
原典を補う、主商・完備化の外延性と明示的な可換図式による経路。

## 規約

H/d の p 完備性 hT はこのファイルで解消せず、H 自体の prism 性も結論しない。
条件付きの入力作用を含む普遍性を絶対 envelope の同定完了とは数えない。

## 使われ方

並列成果から完備性・生成元正則性が到着したときの絶対 envelope 比較の合流点。
-/

@[expose] public noncomputable section PowerRootPrismMonicOriginalInputSquare

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
variable (hf : f.Monic)

set_option maxHeartbeats 800000 in
-- 元の H⁰ と完備入力の依存する環構造・係数作用を同時に照合するため。
/-- 概要：完備入力図式の可換性は全ての標準根の保存と同値。
方針：標的の p 完備性を有界試験 prism から供給し、係数と全根の外延性を使う。
規約：H/d の p 完備性を明示仮定にする。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力作用を含む普遍性。 -/
theorem powerRootPrismMonicOriginalInputSquare_iff_roots
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ (hT : IsAdicComplete (Ideal.span {(p : T)}) T)
      (F : H →+* B) (hF : F.comp baseH = k.toRingHom),
      (powerRootPrismMonicReductionMap W hW f Q k F hF).comp
        (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η ↔
          ∀ n, qB (F (uL (jL (powerRootPolynomialVariable A p hp n)))) =
            η (lS (powerRootPolynomialVariable R p hp n)) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT F hF
  let : IsAdicComplete (Ideal.span {(p : B ⧸ Q.ideal)}) (B ⧸ Q.ideal) :=
    _root_.SerrePositivity.BhattScholze.boundedPrism_quotient_isAdicComplete_prime Q hB
  constructor
  · intro hs n
    have h := RingHom.congr_fun hs (lS (powerRootPolynomialVariable R p hp n))
    rw [RingHom.comp_apply, powerRootPrismMonicOriginalInputMap_root] at h
    exact h
  · intro hr
    apply powerRootMonicCompletedInput_ringHom_ext p hp fR
    · apply RingHom.ext
      intro x
      change powerRootPrismMonicReductionMap W hW f Q k F hF
        (powerRootPrismMonicOriginalInputMap W hW f hf hT (lS (algebraMap R PR x))) =
          η (lS (algebraMap R PR x))
      have hc := RingHom.congr_fun (powerRootPrismMonicOriginalInputMap_coeff W hW f hf hT) x
      change powerRootPrismMonicOriginalInputMap W hW f hf hT
        (lS (algebraMap R PR x)) = φ₀ x at hc
      rw [hc]
      exact (RingHom.congr_fun (powerRootPrismMonicReductionMap_coeff W hW f Q k F hF) x).trans
        (RingHom.congr_fun hη x).symm
    · intro n
      change powerRootPrismMonicReductionMap W hW f Q k F hF
        (powerRootPrismMonicOriginalInputMap W hW f hf hT
          (lS (powerRootPolynomialVariable R p hp n))) =
            η (lS (powerRootPolynomialVariable R p hp n))
      rw [powerRootPrismMonicOriginalInputMap_root]
      exact hr n

set_option maxHeartbeats 800000 in
-- 元の H⁰ と完備入力図式の依存型を保ったまま一意存在を移すため。
/-- 概要：原典の完備入力作用を保つ H から有界試験 prism への δ 射は一意に存在。
方針：根保存の普遍性を、完備入力図式の可換性との同値で言い換える。
規約：hT と H 自体の prism 性の解消は別工程に残す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope 比較の入力作用を含む接続点。 -/
theorem existsUnique_powerRootPrismMonicHom_preserving_original_input
    (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
      (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)
    (η : SI →+* B ⧸ Q.ideal)
    (hη : (η.comp lS).comp (algebraMap R PR) = k.quotientMap) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hT : IsAdicComplete (Ideal.span {(p : T)}) T,
    ∃! F : H →+* B, (DH).IsDeltaHom Q.deltaStructure F ∧
      ∃ hF : F.comp baseH = k.toRingHom,
        (powerRootPrismMonicReductionMap W hW f Q k F hF).comp
          (powerRootPrismMonicOriginalInputMap W hW f hf hT) = η := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hT
  obtain ⟨F, hF, hu⟩ := existsUnique_powerRootPrismMonicCompletionHom_of_original_completed_input
    W hW f hf Q hB k η hη
  refine ⟨F, ⟨hF.1, ⟨hF.2.1, ?_⟩⟩, ?_⟩
  · exact (powerRootPrismMonicOriginalInputSquare_iff_roots W hW f Q k hf hB η hη hT F hF.2.1).mpr
      (hF.2.2)
  · rintro K ⟨hKδ, hK, hs⟩
    exact hu K ⟨hKδ, hK,
      (powerRootPrismMonicOriginalInputSquare_iff_roots W hW f Q k hf hB η hη hT K hK).mp hs⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicOriginalInputSquare

/-! ## André A1-a：正則性を明示した源 prism の入力作用を保つ普遍性

## 概要

H の生成元正則性と H/d の p 完備性を明示すると、原典の完備入力作用を保つ
H の prism から有界試験 prism への射は一意に存在する。BS 著者版 Remark 7.15（著者版 p.62）。

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

@[expose] public noncomputable section PowerRootPrismMonicSourcePrismUniversal

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の δ 普遍性から prism 普遍性への移送。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の環射の一意性の移送。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底上の prism 射。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備入力図式を prism 射で表す。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の絶対 prismatic envelope の合流点。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界源から完備入力作用への接続。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の有界源の絶対 envelope への合流点。 -/
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

end PowerRootPrismMonicSourcePrismUniversal

/-! ## André A1-a：元の H の入力作用を持つ対象と初期性

## 概要

生成元正則性と H/d の有界 p ねじれが供給されたとき、元の H を原典の完備入力作用を持つ
有界 prism の対象とし、その圏で初期であることを証明する。
BS 著者版 Remark 7.15（著者版 p.62）の envelope 比較の合流点。

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

@[expose] public noncomputable section PowerRootPrismMonicEnvelopeInitial

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の源の初期性を述べる対象。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の envelope の初期性への条件付き接続。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の原典の普遍性との条件付き同定。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の H と envelope の実環としての比較。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の比較同型の係数作用の確認。 -/
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

end PowerRootPrismMonicEnvelopeInitial

/-! ## 完全試験 prism の剰余根データによる実完備化の普遍性

## 概要

完全試験 prism の商に互換根列を指定し、その第零根が元の多項式の根なら、
raw 実完備化から試験 prism へ基底と剰余根を保つ δ 射が一意に存在する。
BS 著者版 Remark 7.15（著者版 p.62）の絶対 envelope 比較の完全試験環での段階。

## 方針

共通完備商で入力 δ 射を一意に持ち上げ、元の raw 割り算・実完備化の普遍性を適用する。
原典とは異なる Perfection のモノイド同型・有理指数評価・W₂ 切断による経路。

## 規約

試験 prism の完全性と指定生成元の一致を明示する。
源の prism 商の p 正則性・入力のモニック性は、この普遍射には不要。
一般の試験 prism と絶対 envelope 全体との同定は別工程。

## 使われ方

試験環内の実根列も指定入力 δ 射も引数に残さず、商内の根データから比較射を作る。
-/

@[expose] public noncomputable section PowerRootPrismMonicResidueRootUniversal

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


/-- 概要：完全試験 prism の剰余根データを保つ実完備化からの δ 射は一意に存在。
方針：一意な入力 δ 持上げで分子の可除性を得て、raw 実完備化の普遍性を使う。
規約：根列は商内だけに指定する。試験 prism の完全性と生成元の一致は前提に残す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完全試験 prism への絶対入力データによる比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom_of_perfect_residue_roots
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (hQ : Q.deltaStructure.IsPerfect)
    (k : A →+* B) (hk : W.deltaStructure.IsDeltaHom Q.deltaStructure k)
    (hd : k W.generator = Q.generator)
    (ρ : ℕ → B ⧸ Q.ideal) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hroot : f.eval₂ ((Ideal.Quotient.mk Q.ideal).comp k) (ρ 0) = 0) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (DH).IsDeltaHom Q.deltaStructure F ∧
        F.comp (powerRootPrismMonicCompletionBaseMap W hW f) = k ∧
          ∀ n, Ideal.Quotient.mk Q.ideal
            (F (uL (jL (powerRootPolynomialVariable A p hp n)))) = ρ n := by
  let := pdCompletionCommRing L p (jL dP)
  let qB := Ideal.Quotient.mk Q.ideal
  obtain ⟨g, hg, hgu⟩ :=
    existsUnique_powerRootPolynomialDeltaHom_of_perfectPrism_residue_roots p hW.p_mul_injective
      W.deltaStructure Q hQ k hk ρ hρ
  have hdg : g dP = Q.generator := (RingHom.congr_fun hg.2.1 W.generator).trans hd
  have hinput : g (powerRootMonicPDInput p f) =
      f.eval₂ k (g (powerRootPolynomialVariable A p hp 0)) := by
    unfold powerRootMonicPDInput powerRootPolynomialBaseMap
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hg.2.1]
  have hzero : qB (g (powerRootMonicPDInput p f)) = 0 := by
    calc
      _ = qB (f.eval₂ k (g (powerRootPolynomialVariable A p hp 0))) := congrArg qB hinput
      _ = f.eval₂ (qB.comp k) (qB (g (powerRootPolynomialVariable A p hp 0))) :=
        Polynomial.hom_eval₂ f k qB _
      _ = 0 := by
        rw [show qB (g (powerRootPolynomialVariable A p hp 0)) = ρ 0 from hg.2.2 0]
        exact hroot
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hdg]
    exact Q.generator_regular
  have ha : ∀ s, g dP ∣ g (a s) := by
    intro s
    rw [hdg]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hdg]
    exact Q.complete_generator
  obtain ⟨F, hF, hu⟩ := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg.1 hr ha
    Q.complete_p hc
  refine ⟨F, ⟨hF.1, ?_, ?_⟩, ?_⟩
  · change (F.comp ((uL).comp jL)).comp (algebraMap A P) = k
    rw [hF.2]
    exact hg.2.1
  · intro n
    exact (congrArg qB (RingHom.congr_fun hF.2 (powerRootPolynomialVariable A p hp n))).trans
      (hg.2.2 n)
  · intro K hK
    let gK := K.comp ((uL).comp jL)
    have hKδ : (E).IsDeltaHom Q.deltaStructure gK :=
      hK.1.comp ((pdCompletionUnit_isDeltaHom DL (jL dP)).comp
        (deltaAdjoinDivisionMap_isDeltaHom E dP a))
    have hgK : gK = g := hgu gK ⟨hKδ, hK.2.1, hK.2.2⟩
    exact hu K ⟨hK.1, hgK⟩

end SerrePositivity.BhattScholze.Andre

end PowerRootPrismMonicResidueRootUniversal
