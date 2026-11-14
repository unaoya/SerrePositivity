module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarCokernelTensor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear

/-!
# 完備分冪係数の完備化同値

## 概要
未完備項から完備項への単位は、各有限冪商で同型を誘導する。
任意の加群とのテンソル積にも移せる。

## 方針
加群の冪商をスカラー作用の余核として読み、実際の単位が誘導する余核射を比較する。

## 規約
p の正則性は基底環に課す。

## 使われ方
BS 著者版 Theorem 6.4 の未完備分冪列から完備列への移行。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "Raw" => ModuleCat.of k (pdRaw k r n)
local notation "Term" => ModuleCat.of k (pdTerm p k r n)
local notation "U" => ModuleCat.ofHom (AlgHom.toLinearMap (pdTermCompletionUnitAlg p k r n))

private def scalarQuotientIso (M : ModuleCat.{u} k) (e : ℕ) :
    cokernel ((p : k)^e • 𝟙 M) ≅ modulePowerReduction (p : k) M e :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (modulePowerReductionShortComplex_exact (p : k) M e).gIsCokernel

@[reassoc] private theorem scalarQuotientIso_π (M : ModuleCat.{u} k) (e : ℕ) :
    cokernel.π ((p : k)^e • 𝟙 M) ≫ (scalarQuotientIso p k M e).hom =
      modulePowerReductionMap (p : k) M e :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (modulePowerReductionShortComplex_exact (p : k) M e).gIsCokernel WalkingParallelPair.one

include hr

/-- 実際の完備化単位は、各冪のスカラーの余核で同型を誘導する。 -/
theorem pdTermCompletionUnit_cokernel_isIso (e : ℕ) :
    IsIso (cokernel.map ((p : k)^e • 𝟙 Raw) ((p : k)^e • 𝟙 Term) U U
      (by simp [Linear.smul_comp, Linear.comp_smul])) := by
  let f := cokernel.map ((p : k)^e • 𝟙 Raw) ((p : k)^e • 𝟙 Term) U U
    (by simp [Linear.smul_comp, Linear.comp_smul])
  let q := (pdTermReductionEquiv p k r n hr e).toModuleIso
  have h : f ≫ (scalarQuotientIso p k Term e).hom ≫ q.hom =
      (scalarQuotientIso p k Raw e).hom := by
    apply (cancel_epi (cokernel.π ((p : k)^e • 𝟙 Raw))).mp
    simp only [f, cokernel.map, Category.assoc, cokernel.π_desc_assoc,
      scalarQuotientIso_π_assoc, scalarQuotientIso_π]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact pdTermReductionEquiv_unit p k r n hr e x
  have hIso : IsIso (f ≫ (scalarQuotientIso p k Term e).hom ≫ q.hom) := by
    rw [h]
    infer_instance
  have hi : IsIso (f ≫ (scalarQuotientIso p k Term e).hom) :=
    IsIso.of_isIso_comp_right _ q.hom
  exact IsIso.of_isIso_comp_right f (scalarQuotientIso p k Term e).hom

/-- 任意の形式の因子をテンソルしても完備化単位は各冪商で同型を誘導する。 -/
theorem pdTermCompletionUnit_tensor_cokernel_isIso (e : ℕ) (V : ModuleCat.{u} k) :
    IsIso (cokernel.map ((p : k)^e • 𝟙 (Raw ⊗ V)) ((p : k)^e • 𝟙 (Term ⊗ V))
      ((tensorRight V).map U) ((tensorRight V).map U)
      (by simp [Linear.smul_comp, Linear.comp_smul])) :=
  tensorRight_scalarCokernelMap_isIso ((p : k)^e) U V
    (pdTermCompletionUnit_cokernel_isIso p k r n hr e)

end SerrePositivity.BhattScholze.Prismatic
