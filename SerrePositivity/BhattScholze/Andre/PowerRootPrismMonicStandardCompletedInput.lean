module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicStandardEquationInput
public import SerrePositivity.BhattScholze.Andre.PowerRootMonicCompletedInput

/-!
# André A1-a：完備入力環から H/d への標準射の接続

## 概要

H/d の通常の p 完備性を明示仮定にすると、原典の順序の完備入力環から H/d への
係数と全根を保つ標準射を構成できる。BS Rem 7.15（著者版 p.62）の入力作用。

## 方針

通常の入力射を p 完備化から一意に延長し、モニック入力の商と完備化の交換同型を合成する。
原典を補う主商と完備化の明示的な普遍性による経路。

## 規約

H/d の p 完備性はこのファイルで証明せず明示引数にする。hpR で代用しない。
源 H の prism 性と絶対 envelope 全体の同定は別工程。

## 使われ方

並列成果から通常の p 完備性が供給された時点で、原典の完備入力作用を接続する。
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
使われ方：BS Rem 7.15（著者版 p.62）の S→H/d の条件付き接続点。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の完備入力作用の根・係数の追跡。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の基底上の完備入力図式。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の完備入力図式を全根で確認する。 -/
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
