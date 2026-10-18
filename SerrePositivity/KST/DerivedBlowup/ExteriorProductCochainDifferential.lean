module

public import SerrePositivity.KST.DerivedBlowup.ExteriorProductCochainComponents
public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerDifferential

/-!
概要：KST Def3.1 の整数次数での生成元追加の微分行列。
方針：総外積への単射で、証明済みの収縮の二成分公式を比較する。
規約：第一成分が shifted 項、微分は (-dx,ax+dy)。
使われ方：反復 cone との比較の chain 条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：最後の座標での収縮成分と Koszul 微分は反可換。
方針：微分後の二成分分解に第一射影を適用する。
規約：KST Def3.1。使われ方：cone の shifted 成分の符号。 -/
theorem exteriorProductTail_contract (d : M →ₗ[R] R) (a : R)
    (z : ExteriorAlgebra R (M × R)) :
    exteriorProductTail
        (CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a) z) =
      -CliffordAlgebra.contractLeft (Q := 0) d (exteriorProductTail z) := by
  rw [exteriorProduct_contract_decomposition, exteriorProductTail_join]

/-- 概要：射影後の Koszul 微分は元の微分と追加成分の a 倍の和。
方針：微分後の二成分分解に第二射影を適用する。
規約：KST Def3.1。使われ方：cone 微分の非対角成分。 -/
theorem exteriorProductOut_contract (d : M →ₗ[R] R) (a : R)
    (z : ExteriorAlgebra R (M × R)) :
    exteriorProductOut
        (CliffordAlgebra.contractLeft (Q := 0) (exteriorProductDifferential d a) z) =
      a • exteriorProductTail z +
        CliffordAlgebra.contractLeft (Q := 0) d (exteriorProductOut z) := by
  rw [exteriorProduct_contract_decomposition, exteriorProductOut_join]

/-- 概要：整数 cochain の二成分分解は cone 微分の行列と適合する。
方針：各成分を総外積に包含し、収縮公式と包含の微分適合性を使う。
規約：KST Def3.1、q 次から q+1 次。使われ方：mappingCone 比較同型の chain 条件。 -/
theorem exteriorProductCochainEquiv_d (d : M →ₗ[R] R) (a : R) (q : ℤ)
    (z : (exteriorKoszulCochain (exteriorProductDifferential d a)).X q) :
    exteriorProductCochainEquiv d a (q + 1)
        (((exteriorKoszulCochain (exteriorProductDifferential d a)).d q (q + 1)).hom z) =
      (-((exteriorKoszulCochain d).d (q + 1) (q + 1 + 1)).hom
          (exteriorProductCochainEquiv d a q z).1,
        a • (exteriorProductCochainEquiv d a q z).1 +
          ((exteriorKoszulCochain d).d q (q + 1)).hom (exteriorProductCochainEquiv d a q z).2) := by
  apply Prod.ext
  · apply exteriorCochainInclusion_injective d (q + 1 + 1)
    change exteriorCochainInclusion d (q + 1 + 1)
      (exteriorProductCochainEquiv d a (q + 1)
        (((exteriorKoszulCochain (exteriorProductDifferential d a)).d q (q + 1)).hom z)).1 =
      exteriorCochainInclusion d (q + 1 + 1)
        (-((exteriorKoszulCochain d).d (q + 1) (q + 1 + 1)).hom
          (exteriorProductCochainEquiv d a q z).1)
    rw [exteriorProductCochainEquiv_fst, exteriorCochainInclusion_d, map_neg,
      exteriorCochainInclusion_d, exteriorProductCochainEquiv_fst]
    exact exteriorProductTail_contract d a _
  · apply exteriorCochainInclusion_injective d (q + 1)
    change exteriorCochainInclusion d (q + 1)
      (exteriorProductCochainEquiv d a (q + 1)
        (((exteriorKoszulCochain (exteriorProductDifferential d a)).d q (q + 1)).hom z)).2 =
      exteriorCochainInclusion d (q + 1)
        (a • (exteriorProductCochainEquiv d a q z).1 +
          ((exteriorKoszulCochain d).d q (q + 1)).hom (exteriorProductCochainEquiv d a q z).2)
    rw [exteriorProductCochainEquiv_snd, exteriorCochainInclusion_d, map_add, map_smul,
      exteriorCochainInclusion_d, exteriorProductCochainEquiv_fst, exteriorProductCochainEquiv_snd]
    exact exteriorProductOut_contract d a _

end SerrePositivity.KST.DerivedBlowup
