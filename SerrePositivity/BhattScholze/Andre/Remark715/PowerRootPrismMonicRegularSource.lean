module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootPrismMonicCompletionPrism
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom

/-!
# André A1-a：生成元正則性を明示した元の H の prism 構造

## 概要

元の H の標準分母像の正則性が供給されると、同じ H はその像を生成元とする prism となる。
基底からの標準射も prism 射になる。BS Rem 7.15（著者版 p.62）の源の合流点。

## 方針

標準 δ 射で distinguished 性を移し、既存の導来完備性と指定された正則性を組み合わせる。
原典を補う raw 実完備化の明示的な構造による経路。

## 規約

正則性 hreg は明示引数とし、ここでは解消しない。hpR・モニック性で代用しない。
既存の hpR 付き定理を変更せず、別名で合流先を用意する。

## 使われ方

並列の生成元正則性の成果を受け取り、元の H の prism 射による初期性へ接続する。
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

local notation "dH" => uL (jL dP)
local notation "baseH" => powerRootPrismMonicCompletionBaseMap W hW f

/-- 概要：標準分母像が正則なら元の H を prism として構成できる。
方針：distinguished 性を raw 射と完備化単位で移し、二方向の導来完備性を使う。
規約：hreg を明示し、完全 prism とは主張しない。
使われ方：BS Rem 7.15（著者版 p.62）の源の prism 化への条件付き接続点。 -/
def powerRootPrismMonicCompletionPrismOfRegular :
    let := pdCompletionCommRing L p (jL dP)
    IsSMulRegular H dH → OrientedPrism p H := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  have hdL : (DL).IsDistinguished (jL dP) := by
    have h := (powerRootPrismGenerator_isDistinguished W hW).map jL
    rw [deltaAdjoinDivisionMap_isDeltaHom E dP a dP] at h
    exact h
  have hdH : (DH).IsDistinguished dH := by
    have h := hdL.map uL
    rw [pdCompletionUnit_isDeltaHom DL (jL dP) (jL dP)] at h
    exact h
  exact OrientedPrism.ofDistinguished DH dH hdH hreg
    (pdCompletionH0_self_complete_p L p (jL dP))
    (pdCompletionH0_self_complete_d L p (jL dP))

/-- 概要：条件付き prism の生成元は元の標準分母像そのもの。
方針：構成の生成元の定義を確認する。
規約：orientation を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の H/d の保持。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_generator :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).generator = dH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：条件付き prism の δ 構造は元の実完備化の δ 構造。
方針：構成の δ 構造の定義を確認する。
規約：台環も δ 構造も取り替えない。
使われ方：BS Rem 7.15（著者版 p.62）の既存の δ 普遍射との接続。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_deltaStructure :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).deltaStructure = DH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：条件付き prism のイデアルは元の標準分母像の主イデアル。
方針：元の orientation による prism イデアルの定義を使う。
規約：同じ H/d を標準商として使う。
使われ方：BS Rem 7.15（著者版 p.62）の既存の標準入力作用の保持。 -/
theorem powerRootPrismMonicCompletionPrismOfRegular_ideal :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg).ideal = Ideal.span {dH} := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

/-- 概要：元の基底射は条件付き構成した H の prism への射となる。
方針：既存の δ 保存性と標準生成元像によるイデアル保存性を組み合わせる。
規約：基底の指定生成元を元の標準分母像へ送る。
使われ方：BS Rem 7.15（著者版 p.62）の基底 prism 上の源。 -/
def powerRootPrismMonicCompletionPrismBaseHomOfRegular :
    let := pdCompletionCommRing L p (jL dP)
    (hreg : IsSMulRegular H dH) →
      OrientedPrism.Hom W (powerRootPrismMonicCompletionPrismOfRegular W hW f hreg) := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  refine ⟨baseH, powerRootPrismMonicCompletionBaseMap_isDeltaHom W hW f, ?_⟩
  change Ideal.span {W.generator} ≤ (Ideal.span {dH}).comap baseH
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = W.generator := Set.mem_singleton_iff.mp hx
  rw [hxd]
  exact Ideal.mem_span_singleton_self dH

/-- 概要：条件付き基底 prism 射の台の環射は元の標準係数射。
方針：構成の環射の定義を使う。
規約：係数作用を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の基底保存条件の照合。 -/
theorem powerRootPrismMonicCompletionPrismBaseHomOfRegular_toRingHom :
    let := pdCompletionCommRing L p (jL dP)
    ∀ hreg : IsSMulRegular H dH,
      (powerRootPrismMonicCompletionPrismBaseHomOfRegular W hW f hreg).toRingHom = baseH := by
  let := pdCompletionCommRing L p (jL dP)
  dsimp only
  intro hreg
  rfl

end SerrePositivity.BhattScholze.Andre
