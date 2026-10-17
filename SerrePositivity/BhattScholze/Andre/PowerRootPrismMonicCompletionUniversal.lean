module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionPrism
public import SerrePositivity.BhattScholze.Andre.RawDeltaDivisionPDTorsionComparison

/-!
# André E1・E2：具体的な実完備化 prism の普遍性と一段構成比較

## 概要

無限根モニック実完備化 prism は、指定した入力 δ 射と分子の可除性を持つ試験 prism へ
一意に写る。さらに旧分母ねじれ除去を挟む既存一段構成と環同型となる。
BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の比較の代数的部分。

## 方針

試験 prism の正則性と完備性を raw 実完備化の一般普遍性に供給する。
自分自身で証明した分母正則性から旧ねじれ除去の標準比較を適用する。
その正則性は原典と異なる実源の純性による経路で供給する。

## 規約

無限根入力環からの δ 射を指定する相対的普遍性である。
prism 商の p 正則性や正次数は要求しない。
原典の絶対 prismatic envelope の同定は、この入力射の一意持上げとの接続を要する。

## 使われ方

元の実候補を既存の一段 δ 完全化へ渡すための係数を保つ比較。
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
variable (f : Polynomial A) (hf : f.Monic)
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


include hf in
/-- 概要：指定入力 δ 射と可除性を持つ試験 prism への射は一意に存在する。
方針：試験 prism の正則性・p 完備性・生成元完備性を一般の raw 普遍性へ渡す。
規約：生成元の像の一致を明示し、入力射自体は指定する。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の相対 envelope 比較。 -/
theorem existsUnique_powerRootPrismMonicCompletionHom
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hg : (E).IsDeltaHom Q.deltaStructure g) (hd : g dP = Q.generator)
    (ha : Q.generator ∣ g (powerRootMonicPDInput p f)) :
    let := pdCompletionCommRing L p (jL dP)
    ∃! F : H →+* B,
      (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
        Q.deltaStructure F ∧ F.comp ((uL).comp jL) = g := by
  let := pdCompletionCommRing L p (jL dP)
  have hr : Function.Injective (fun x : B => g dP * x) := by
    rw [hd]
    exact Q.generator_regular
  have hc : IsModuleComplete B (g dP) (ModuleCat.of B B) := by
    rw [hd]
    exact Q.complete_generator
  have ha' : ∀ s, g dP ∣ g (a s) := by
    intro s
    change g dP ∣ g (powerRootMonicPDInput p f)
    rw [hd]
    exact ha
  have h := existsUnique_rawDeltaDivisionPDHom E Q.deltaStructure dP a g hg hr ha'
    Q.complete_p hc
  change ∃! F : H →+* B, (DH).IsDeltaHom Q.deltaStructure F ∧
    F.comp ((uL).comp jL) = g
  exact h

include hf in
/-- 概要：元の無限根モニック実完備化は旧ねじれ除去後の既存一段実完備化と環同型。
方針：自分自身の分母正則性を一般の標準比較に供給する。
規約：元の実 H⁰ を源とし、比較先の正則性を追加仮定しない。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の一段構成との接続。 -/
def powerRootPrismMonicCompletionTorsionEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    H ≃+* DerivedDeltaDivisionCompletion E dP a := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf)

include hf in
/-- 概要：一段構成比較は無限根入力環の標準係数像を保つ。
方針：一般比較の raw 代表元公式を標準入力射に適用する。
規約：全ての入力環元を扱う。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の後続 δ 完全化比較。 -/
theorem powerRootPrismMonicCompletionTorsionEquiv_coeff (r : P) :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    powerRootPrismMonicCompletionTorsionEquiv W hW f hf (uL (jL r)) =
      derivedDeltaDivisionMap E dP a r := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv_unit E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf) (jL r)

include hf in
/-- 概要：具体的な一段構成比較は実完備化 prism の δ 構造を保つ。
方針：一般比較の δ 性へ分母正則性を供給する。
規約：原典の絶対 envelope との比較は別工程。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の既存 δ 完全化への接続。 -/
theorem powerRootPrismMonicCompletionTorsionEquiv_isDeltaHom :
    let := pdCompletionCommRing L p (jL dP)
    let := derivedDeltaDivisionCommRing E dP a
    (powerRootPrismMonicCompletionPrism W hW f hf).deltaStructure.IsDeltaHom
      (derivedDeltaDivisionStructure E dP a)
      (powerRootPrismMonicCompletionTorsionEquiv W hW f hf).toRingHom := by
  let := pdCompletionCommRing L p (jL dP)
  let := derivedDeltaDivisionCommRing E dP a
  exact rawDeltaDivisionPDTorsionEquiv_isDeltaHom E dP a
    (powerRootPrismMonicRaw_pdCompletion_generator_regular W hW f hf)

include hf in
/-- 概要：入力射と両立する比較射は指定 prism 生成元を保つ。
方針：入力環上の合成等式を分母で評価する。
規約：射の δ 性に依存しない生成元の計算。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の相対 prism 射の条件。 -/
theorem powerRootPrismMonicCompletionHom_generator
    {B : Type u} [CommRing B] (Q : OrientedPrism p B) (g : P →+* B)
    (hd : g dP = Q.generator) :
    let := pdCompletionCommRing L p (jL dP)
    ∀ F : H →+* B, F.comp ((uL).comp jL) = g →
      F (powerRootPrismMonicCompletionPrism W hW f hf).generator = Q.generator := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro F hF
  exact (RingHom.congr_fun hF dP).trans hd

end SerrePositivity.BhattScholze.Andre
