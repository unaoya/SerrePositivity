module
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeBiprodExact
public import SerrePositivity.DifferentialGraded.Complexes.ConeDesc
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # 二成分 mapping cocone の元の短完全列の cofiber 比較
概要：第二 cocone から全 cocone への同じ包含の円錐は、元の第一成分へ準同型となる。
方針：元の次数別分裂短完全列を、同じ零比較の標準円錐射へ適用する。
規約：両成分・包含・射影を保つ。使われ方：二軸 Yoneda 円錐比較の準同型判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R] {K L T : Complex R} (a : K ⟶ T) (b : L ⟶ T)

/-- 同じ第二 cocone 包含の円錐から、元の第一成分への実比較鎖写像。 -/
def mappingCoconeBiprodConeComparison :
    mappingCone (complexMappingCoconeBiprodInclusion a b) ⟶ K :=
  complexConeDesc (complexMappingCoconeBiprodInclusion a b)
    (complexMappingCoconeBiprodProjection a b)
    (complexMappingCoconeBiprodInclusion_projection a b)

/-- 同じ円錐比較は、元の全 cocone からの第一射影を厳密に回収する。 -/
lemma mappingCoconeBiprodConeComparison_inr :
    mappingCone.inr (complexMappingCoconeBiprodInclusion a b) ≫
      mappingCoconeBiprodConeComparison a b = complexMappingCoconeBiprodProjection a b :=
  complexConeDesc_inr _ _ _

/-- 元の次数別分裂短完全列により、同じ円錐比較は実準同型。 -/
lemma mappingCoconeBiprodConeComparison_quasiIso :
    QuasiIso (mappingCoconeBiprodConeComparison a b) := by
  change QuasiIso (mappingCone.descShortComplex (complexMappingCoconeBiprodShortComplex a b))
  exact mappingCone.quasiIso_descShortComplex
    (complexMappingCoconeBiprodShortComplex_shortExact a b)

end SerrePositivity.KST.SConstruction
