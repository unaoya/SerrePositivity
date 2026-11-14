module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermCompletionEquivalence
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamColumnBounded
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalClassicalComparison
public import Mathlib.RingTheory.Regular.IsSMulRegular
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarCokernelTensor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDRawColumnCompletion
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermReductionLinear
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 分冪 de Rham 列の完備化同値

## 概要
未完備の自由列から完備列への単位は、導来 p 完備化の後で擬同型になる。

## 方針
各次数の有限冪商で同型を示し、正則なスカラーの余核と Koszul 商の比較を適用する。

## 規約
基底環は p 正則。完備列の各項の平坦性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4 の第 0 列で完備導来底変換を自由模型から計算する。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.DerivedCompletion
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ) (n : SimplexCategory)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "Raw" => pdRaw k r n.len
local notation "Term" => pdTerm p k r n.len
local notation "Copies" => ((Fin r × Fin (n.len + 1)) →₀ k)
local notation "K" => pdUncompletedColumn k r n
local notation "L" => pdDeRhamColumn p k r n
local notation "η" => pdColumnCompletionUnit p k r n
local notation "emb" => ComplexShape.embeddingUpNat

include hr

private theorem forms_regular (j : ℕ) :
    IsSMulRegular ((K).X j) (p : k) ∧ IsSMulRegular ((L).X j) (p : k) := by
  let e := Fintype.equivFin (Fin r × Fin (n.len + 1))
  let : LinearOrder (Fin r × Fin (n.len + 1)) := LinearOrder.lift' e e.injective
  let b : Module.Basis (Fin r × Fin (n.len + 1)) k Copies := Finsupp.basisSingleOne
  let : Module.Free k (⋀[k]^j Copies) := Module.Free.of_basis (b.exteriorPower j)
  have hRaw : IsSMulRegular Raw (p : k) := by
    intro x y hxy
    apply PDSmallRawEnvelope.raw_regular p r n.len hr
    simpa only [Nat.cast_smul_eq_nsmul] using hxy
  have hTerm : IsSMulRegular Term (p : k) := by
    have h := principalCompletionH0_smul_injective_of_regular Raw (p : Raw)
      (PDSmallRawEnvelope.raw_regular p r n.len hr)
    intro x y hxy
    apply h
    simpa only [Nat.cast_smul_eq_nsmul] using hxy
  exact ⟨hRaw.rTensor (⋀[k]^j Copies), hTerm.rTensor (⋀[k]^j Copies)⟩

private theorem term_quotient_isIso (e j : ℕ) :
    IsIso ((scalarCokernelFunctor ((p : k)^e)).map ((η).f j)) := by
  exact pdTermCompletionUnit_tensor_cokernel_isIso p k r n.len hr e
    (ModuleCat.of k (⋀[k]^j Copies))

private theorem extended_forms_regular (i : ℤ) :
    IsSMulRegular (((K).extend emb).X i) (p : k) ∧
      IsSMulRegular (((L).extend emb).X i) (p : k) := by
  by_cases h : ∃ j, (emb).f j = i
  · obtain ⟨j,rfl⟩ := h
    have hR := (forms_regular p k r n hr j).1
    have hT := (forms_regular p k r n hr j).2
    exact ⟨(((K).extendXIso emb rfl).toLinearEquiv.isSMulRegular_congr (p : k)).mpr hR,
      (((L).extendXIso emb rfl).toLinearEquiv.isSMulRegular_congr (p : k)).mpr hT⟩
  · have hR := (K).isZero_extend_X emb i (fun j hj => h ⟨j,hj⟩)
    have hT := (L).isZero_extend_X emb i (fun j hj => h ⟨j,hj⟩)
    constructor
    · exact fun x y _ => (ModuleCat.isZero_iff_subsingleton.mp hR).elim x y
    · exact fun x y _ => (ModuleCat.isZero_iff_subsingleton.mp hT).elim x y

private theorem extended_quotient_isIso (e : ℕ) :
    IsIso (powerCokernelMap (p : k) (HomologicalComplex.extendMap η emb) e) := by
  apply powerCokernelMap_isIso_of_components
  intro i
  let F := scalarCokernelFunctor ((p : k)^e)
  change IsIso (F.map ((HomologicalComplex.extendMap η emb).f i))
  by_cases h : ∃ j, (emb).f j = i
  · obtain ⟨j,rfl⟩ := h
    rw [HomologicalComplex.extendMap_f η emb rfl, Functor.map_comp, Functor.map_comp]
    have : IsIso (F.map ((η).f j)) := term_quotient_isIso p k r n hr e j
    infer_instance
  · have hR := (K).isZero_extend_X emb i (fun j hj => h ⟨j,hj⟩)
    have hT := (L).isZero_extend_X emb i (fun j hj => h ⟨j,hj⟩)
    have : IsIso ((HomologicalComplex.extendMap η emb).f i) := hR.isIso hT _
    infer_instance

/-- 未完備分冪列の単位は、整数添字の複体として導来 p 完備化した後で擬同型になる。 -/
theorem pdColumnCompletionUnit_completion_quasiIso :
    QuasiIso ((complexCompletionFunctor k (p : k)).map (HomologicalComplex.extendMap η emb)) := by
  apply complexCompletionFunctor_map_quasiIso_of_powerCokernel (p : k) _
  · exact fun i => (extended_forms_regular p k r n hr i).1
  · exact fun i => (extended_forms_regular p k r n hr i).2
  · intro e
    have := extended_quotient_isIso p k r n hr e
    infer_instance

/-- 列の完備化単位の実際の導来射は、導来 p 完備化の後で同型。 -/
theorem pdColumnCompletionUnit_completion_isIso :
    IsIso ((derivedComplexCompletionFunctor k (p : k)).map
      (DerivedCategory.Q.map (HomologicalComplex.extendMap η emb))) := by
  have := pdColumnCompletionUnit_completion_quasiIso p k r n hr
  have h : IsIso (DerivedCategory.Q.map
      ((complexCompletionFunctor k (p : k)).map (HomologicalComplex.extendMap η emb))) :=
    inferInstance
  exact (NatIso.isIso_map_iff (derivedComplexCompletionComparison k (p : k))
    (HomologicalComplex.extendMap η emb)).mpr h


end SerrePositivity.BhattScholze.Prismatic
