module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.CommutativeAlgebra.DeRham.ExteriorCoefficientMap
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 結晶基底での pd 係数の還元

## 概要
pd 係数の半線形な係数変換を完備 pd 環の商による還元と照合する。

## 方針
完備化単位の上で一致を示し、主完備化への写像の一意性を使う。

## 規約
第 0 外冪を基底環と同定する。

## 使われ方
総複体の第 0 行の射影と Čech 側の Bockstein の比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.DeRham
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "K" => crystallineBase p
local notation "k" => cartierBase p

set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pdModel_modP_coefficient (n : SimplexCategory)
    (x : pdTerm p (crystallineBase.{u} p) r n.len) :
    (pdModel_modP p r).hom.app n (crystallineModPrimeProjection p (pdTerm p K r n.len) x) =
      pdTermCoefficientMap p K k r n.len x := by
  let U := modPrimeMap p (rawUnit p r (crystallineBase.{u} p))
  let V := rawReduction.{u} p r
  let W := rawUnit p r (cartierBase.{u} p)
  let e := pdModel_modP.{u} p r
  let f := crystallineModPrimeProjection p (pdTerm p K r n.len) ≫ e.hom.app n
  let g := ringCatMap p (rawCoeffRing K k r n.len)
  have hUV : U ≫ e.hom = V ≫ W := by
    letI := integralUnit_modPrime_isIso.{u} p r
    letI := rawReduction_isIso.{u} p r
    letI := residualUnit_isIso.{u} p r
    change (asIso U).hom ≫ ((asIso U).symm ≪≫ asIso V ≪≫ asIso W).hom = V ≫ W
    simp [Category.assoc]
  have hfg : f = g := by
    apply ringCat_hom_ext p
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e.hom.app n (crystallineModPrimeProjection p (pdTerm p K r n.len)
      ((rawUnit p r K).app n a)) = _
    let b := crystallineModPrimeProjection p (CommRingCat.of (pdRaw K r n.len)) a
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hUV n) b
    change e.hom.app n (crystallineModPrimeProjection p (pdTerm p K r n.len)
      ((rawUnit p r K).app n a)) = W.app n (pdRawCoefficients K k r n.len a) at h
    rw [h]
    exact (pdTermCoefficientMap_unit p K k r n.len a).symm
  exact ConcreteCategory.congr_hom hfg x

end SerrePositivity.BhattScholze.Prismatic
