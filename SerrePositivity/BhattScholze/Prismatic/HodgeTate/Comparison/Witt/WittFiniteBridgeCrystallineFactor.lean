module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineEnvelopeCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison

/-!
# 有限 Witt 比較の結晶基底を通る分解

## 概要
既存の有限 Witt 比較は、ψ による affine 枠の係数変更と
Witt 結晶基底の小さい橋の合成に一致する。

## 方針
分冪枠の結晶 prism を標的にして、δ 構造、基底脚、頂点変数の p 乗を照合する。

## 規約
ψ に必要な基底と剰余係数の p 正則性、および剰余の p 完備性を明記する。

## 使われ方
BS 著者版 Theorem 6.4 の指定された最初の Witt 比較への結晶の橋の適用。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)
variable {κ κ' : Cardinal.{u}} (X : AffineEnvelopeTerm P Q.n n κ)
variable (V : AffineEnvelopeTerm (wittCrystallinePrism hpC) Q.n n κ')

local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local notation "γ" => wittPdStructure p C hpC hlocalC
local notation "E" => crystallineWittSmallFrameTarget p C hpC hlocalC Q.n n
local notation "T" => crystallineWittSmallFramePrism p C hpC hlocalC Q.n n
local notation "c" => affineEnvelopeCoefficientMap (psiPrism P hpA hpC) X V
local notation "g" => crystallineWittSmallFrameMap p C hpC hlocalC Q.n n V

private theorem wittFiniteBridgeCrystallineFactor_frame :
    (g).comp (c) = (WittFiniteBridge.existsUnique_at P hpA hpC hlocalC hC Q n X).choose := by
  have hg := crystallineWittSmallFrameMap_spec p C hpC hlocalC Q.n n V
  have hc := affineEnvelopeCoefficientMap_spec (psiPrism P hpA hpC) X V
  apply (WittFiniteBridge.existsUnique_at P hpA hpC hlocalC hC Q n X).choose_spec.2
  refine ⟨hg.1.comp hc.1, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hc.2.1]
    change (g).comp (V.X.toHom.toRingHom.comp (psiRing P hpA)) = _
    rw [← RingHom.comp_assoc, hg.2.1]
    rfl
  · intro j i
    change (g) ((c) (X.η (affineVariable P Q.n n j i))) = _
    rw [hc.2.2, hg.2.2]
    rfl

/-- 指定された有限 Witt 比較は、ψ による係数変更と結晶基底上の小さい橋の合成。 -/
theorem wittFiniteBridgeAt_eq_crystalline_comp :
    WittFiniteBridge.finiteBridgeAt P hpA hpC hlocalC hC Q n X =
      (crystallineWittSmallBridgeAt p C hpC hlocalC Q.n n V).comp
        (affineEnvelopeCoefficientMap (psiPrism P hpA hpC) X V) := by
  apply RingHom.ext
  intro x
  apply (crystallineWittSmallFrameEquiv p C hpC hlocalC Q.n n).injective
  change crystallineWittSmallFrameEquiv p C hpC hlocalC Q.n n
      ((crystallineWittSmallFrameEquiv p C hpC hlocalC Q.n n).symm
        ((WittFiniteBridge.existsUnique_at P hpA hpC hlocalC hC Q n X).choose x)) =
    crystallineWittSmallFrameEquiv p C hpC hlocalC Q.n n
      ((crystallineWittSmallFrameEquiv p C hpC hlocalC Q.n n).symm ((g) ((c) x)))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (wittFiniteBridgeCrystallineFactor_frame P hpA hpC hlocalC Q n X V) x).symm

end SerrePositivity.BhattScholze.Prismatic
