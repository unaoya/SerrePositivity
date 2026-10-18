module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDGCategory
public import SerrePositivity.KST.DerivedBlowup.ExteriorMapInclusion

/-!
概要：KST Def3.1 の Koszul 生成元変換は単位と乗法を保つ。
方針：総外積への包含と ExteriorAlgebra.map の代数準同型性を使う。
規約：同一基底環上、微分適合性は明示的な証明。
使われ方：導来 blowup のチャート遷移を dg 関手へ持ち上げる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory MonoidalCategory HomologicalComplex

variable {R M N : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- 概要：Koszul cochain map は単位射を保つ。
方針：単位からの射を次数0の1で評価し、総外積で比較する。
規約：KST Def3.1。使われ方：チャートの dg 関手の map_id。 -/
theorem exteriorKoszulCochainMap_unit (f : M →ₗ[R] N)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (h : dN.comp f = dM) :
    exteriorKoszulUnit dM ≫ exteriorKoszulCochainMap f dM dN h =
      exteriorKoszulUnit dN := by
  apply (DifferentialGraded.unitCycleEquiv (exteriorKoszulCochain dN)).injective
  apply Subtype.ext
  change (exteriorKoszulCochainMap f dM dN h).f 0
    ((exteriorKoszulUnit dM).f 0 (1 : R)) = (exteriorKoszulUnit dN).f 0 (1 : R)
  apply exteriorCochainInclusion_injective dN 0
  rw [exteriorCochainInclusion_map, exteriorKoszulUnit_inclusion,
    exteriorKoszulUnit_inclusion, map_one, map_one, map_one]

/-- 概要：Koszul cochain map は乗法を保つ。
方針：双次数 tensor で包含の自然性と map_mul を使う。
規約：KST Def3.1。使われ方：チャートの dg 関手の map_comp。 -/
theorem exteriorKoszulCochainMap_mul (f : M →ₗ[R] N)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (h : dN.comp f = dM) :
    exteriorKoszulMultiplication dM ≫ exteriorKoszulCochainMap f dM dN h =
      (exteriorKoszulCochainMap f dM dN h ⊗ₘ exteriorKoszulCochainMap f dM dN h) ≫
        exteriorKoszulMultiplication dN := by
  apply DifferentialGraded.tensorHom_ext
  intro p q n hn
  rw [comp_f, ← Category.assoc, exteriorKoszulMultiplication_component,
    comp_f, ← Category.assoc, DifferentialGraded.ι_tensorHom]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (exteriorKoszulCochainMap f dM dN h).f n
    (exteriorCochainBilinear dM p q n hn x y) =
    (exteriorKoszulMultiplication dN).f n
      (ιTensorObj (exteriorKoszulCochain dN) (exteriorKoszulCochain dN) p q n hn
        ((exteriorKoszulCochainMap f dM dN h).f p x ⊗ₜ[R]
          (exteriorKoszulCochainMap f dM dN h).f q y))
  rw [exteriorKoszulMultiplication_apply]
  apply exteriorCochainInclusion_injective dN n
  rw [exteriorCochainInclusion_map, exteriorCochainInclusion_product,
    exteriorCochainInclusion_product, exteriorCochainInclusion_map,
    exteriorCochainInclusion_map, map_mul]

end SerrePositivity.KST.DerivedBlowup
