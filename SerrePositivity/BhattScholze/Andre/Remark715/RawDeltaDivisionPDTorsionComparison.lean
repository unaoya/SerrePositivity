module

public import SerrePositivity.BhattScholze.Andre.Remark715.RawDeltaDivisionPDUniversal
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionPDCompletion

/-!
# André E1・E2：正則な実 raw 完備化と旧ねじれ除去後の実完備化

## 概要

元の raw 包の実完備化で分母像が正則なら、旧分母ねじれの δ 閉包商を先に挟んだ
実完備化と標準 raw 射を保つ環同型となる。
BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の二つの具体的構成の比較。

## 方針

元の実完備化への標準 δ 射は旧ねじれの δ 閉包を殺す。
商からの射を実完備化へ延長し、逆合成を実完備化の環普遍性と商射の全射性で確認する。

## 規約

旧ねじれ除去後の実完備化に新たな正則性を仮定しない。

## 使われ方

無限根モニックの元の実候補を既存の Prop 7.2 の一段構成へ同定する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R σ : Type u} [CommRing R]
variable (D : DeltaStructure p R) (d : R) (a : σ → R)
local notation "B" => DeltaAdjoinDivision D d a
local notation "DB" => deltaAdjoinDivisionStructure D d a
local notation "j" => deltaAdjoinDivisionMap D d a
local notation "H" => PDCompletionH0 B p (j d)
local notation "uB" => pdCompletionUnit B p (j d)
local notation "DH" => deltaPDCompletionStructure DB (j d)
local notation "U" => DeltaDivisionTorsionQuotient D d a
local notation "q" => Ideal.Quotient.mk
  (DeltaStructure.deltaClosure DB (RingHom.ker (algebraMap B (Localization.Away (j d)))))
local notation "jU" => deltaDivisionTorsionMap D d a
local notation "HU" => DerivedDeltaDivisionCompletion D d a
local notation "uU" => pdCompletionUnit U p (jU d)

/-- 概要：元の実 raw 完備化の分母が正則なら旧ねじれ除去を挟む実完備化と環同型。
方針：旧ねじれ商を通る標準射を延長し、係数上の逆合成から完備化の一意性を使う。
規約：新しい正則性は元の実 H⁰ の分母像だけに仮定する。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の一段構成比較。 -/
def rawDeltaDivisionPDTorsionEquiv
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    H ≃+* HU := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  let kB : B →+* HU := (uU).comp q
  have hdB : kB (j d) = derivedDeltaDivisionMap D d a d := rfl
  have hcB : IsModuleComplete HU (kB (j d)) (ModuleCat.of HU HU) := by
    rw [hdB]
    exact derivedDeltaDivision_complete_d D d a
  let F := (existsUnique_pdCompletionRingHom B p (j d) HU kB
    (derivedDeltaDivision_complete_p D d a) hcB).choose
  have hF : F.comp uB = kB := (existsUnique_pdCompletionRingHom B p (j d) HU kB
    (derivedDeltaDivision_complete_p D d a) hcB).choose_spec.1
  let kU := ((DB).existsUnique_torsionReductionHom (j d) DH uB
    (pdCompletionUnit_isDeltaHom DB (j d)) hreg).choose
  have hkU : kU.comp q = uB := ((DB).existsUnique_torsionReductionHom (j d) DH uB
    (pdCompletionUnit_isDeltaHom DB (j d)) hreg).choose_spec.1.1
  have hdU : kU (jU d) = uB (j d) := RingHom.congr_fun hkU (j d)
  have hcU : IsModuleComplete H (kU (jU d)) (ModuleCat.of H H) := by
    rw [hdU]
    exact pdCompletionH0_self_complete_d B p (j d)
  let G := (existsUnique_pdCompletionRingHom U p (jU d) H kU
    (pdCompletionH0_self_complete_p B p (j d)) hcU).choose
  have hG : G.comp uU = kU := (existsUnique_pdCompletionRingHom U p (jU d) H kU
    (pdCompletionH0_self_complete_p B p (j d)) hcU).choose_spec.1
  have hGF : G.comp F = RingHom.id H := by
    apply pdCompletionRingHom_ext B p (j d) H uB
      (pdCompletionH0_self_complete_p B p (j d)) (pdCompletionH0_self_complete_d B p (j d))
    · rw [RingHom.comp_assoc, hF]
      change G.comp ((uU).comp q) = uB
      rw [← RingHom.comp_assoc, hG, hkU]
    · rfl
  have hFG : F.comp G = RingHom.id HU := by
    apply pdCompletionRingHom_ext U p (jU d) HU uU
      (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)
    · rw [RingHom.comp_assoc, hG]
      apply Ideal.Quotient.ringHom_ext
      change (F.comp kU).comp q = (uU).comp q
      rw [RingHom.comp_assoc, hkU, hF]
    · rfl
  exact RingEquiv.ofRingHom F G hFG hGF

/-- 概要：標準比較は元の raw 包の完備化像を旧ねじれ商の標準完備化像へ送る。
方針：順射の実完備化一意延長の合成仕様を評価する。
規約：全ての元の raw 包の元を扱う。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の係数を保つ比較。 -/
theorem rawDeltaDivisionPDTorsionEquiv_unit
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) (r : B) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    rawDeltaDivisionPDTorsionEquiv D d a hreg (uB r) = uU (q r) := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  exact RingHom.congr_fun (existsUnique_pdCompletionRingHom B p (j d) HU ((uU).comp q)
    (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)).choose_spec.1 r

/-- 概要：標準比較は実完備化の指定 δ 構造を保つ。
方針：raw 包からの標準合成が δ 射であることと実完備化の δ 延長性を使う。
規約：環同型の順射について述べる。
使われ方：BS Prop 7.2（著者版 p.55）、Rem 7.15（p.62）の δ 完全化への比較。 -/
theorem rawDeltaDivisionPDTorsionEquiv_isDeltaHom
    (hreg : let := pdCompletionCommRing B p (j d)
      Function.Injective (fun x : H => uB (j d) * x)) :
    let := pdCompletionCommRing B p (j d)
    let := derivedDeltaDivisionCommRing D d a
    (DH).IsDeltaHom (derivedDeltaDivisionStructure D d a)
      (rawDeltaDivisionPDTorsionEquiv D d a hreg).toRingHom := by
  let := pdCompletionCommRing B p (j d)
  let := derivedDeltaDivisionCommRing D d a
  let K := RingHom.ker (algebraMap B (Localization.Away (j d)))
  have hq := (DB).isDeltaHom_quotient_mk ((DB).deltaClosure K) ((DB).isStable_deltaClosure K)
  have hk := (pdCompletionUnit_isDeltaHom (deltaDivisionTorsionStructure D d a) (jU d)).comp hq
  apply pdCompletionRingHom_isDeltaHom DB (j d) (derivedDeltaDivisionStructure D d a)
    ((uU).comp q) hk (derivedDeltaDivision_complete_p D d a) (derivedDeltaDivision_complete_d D d a)
  apply RingHom.ext
  intro r
  exact rawDeltaDivisionPDTorsionEquiv_unit D d a hreg r

end SerrePositivity.BhattScholze.Andre
