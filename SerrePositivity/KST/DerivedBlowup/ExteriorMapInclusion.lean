module

public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerInclusion

/-!
概要：KST Def3.1 の生成元変換と総外積への包含の自然性。
方針：零延長の成分公式で、次数別外積写像に帰着する。
規約：微分を保つ同一基底環上の線形写像。
使われ方：チャート遷移の単位と乗法保存。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R]
  {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 概要：Koszul cochain map は総外積への包含に関して自然。
方針：非正次数で extendMap_f と標準同型の往復を使い、正次数は零対象性を使う。
規約：KST Def3.1、dN∘f=dM。使われ方：乗法と単位の保存。 -/
theorem exteriorCochainInclusion_map (f : M →ₗ[R] N)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (h : dN.comp f = dM)
    (q : ℤ) (z : (exteriorKoszulCochain dM).X q) :
    exteriorCochainInclusion dN q ((exteriorKoszulCochainMap f dM dN h).f q z) =
      ExteriorAlgebra.map f (exteriorCochainInclusion dM q z) := by
  by_cases hq : q ≤ 0
  · simp only [exteriorCochainInclusion, hq, dite_true]
    have hm := HomologicalComplex.extendMap_f (exteriorKoszulChainMap f dM dN h)
      (ComplexShape.embeddingUpIntLE 0) (i := (-q).toNat)
      (i' := q) (by simp only [ComplexShape.embeddingUpIntLE_f, zero_sub]; omega)
    rw [exteriorKoszulCochainMap, hm]
    change (((exteriorCochainXIsoNonpos dN q hq).hom.hom
      ((exteriorCochainXIsoNonpos dN q hq).inv.hom
        (exteriorDegreeMap f (-q).toNat
          ((exteriorCochainXIsoNonpos dM q hq).hom.hom z))))).val = _
    have hi := congr($((exteriorCochainXIsoNonpos dN q hq).inv_hom_id).hom
      (exteriorDegreeMap f (-q).toNat ((exteriorCochainXIsoNonpos dM q hq).hom.hom z)))
    change (exteriorCochainXIsoNonpos dN q hq).hom.hom
      ((exteriorCochainXIsoNonpos dN q hq).inv.hom
        (exteriorDegreeMap f (-q).toNat ((exteriorCochainXIsoNonpos dM q hq).hom.hom z))) =
      exteriorDegreeMap f (-q).toNat ((exteriorCochainXIsoNonpos dM q hq).hom.hom z) at hi
    rw [hi]
    rfl
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos dM q (lt_of_not_ge hq))
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]

end SerrePositivity.KST.DerivedBlowup
