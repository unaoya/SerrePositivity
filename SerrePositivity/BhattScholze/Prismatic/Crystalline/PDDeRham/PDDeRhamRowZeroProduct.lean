module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleCochainCup
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamWedge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamAxisProduct
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleCochainCup

/-!
# 第 0 pd de Rham 行の同型と cup 積

## 概要
外次数零の同型は Alexander–Whitney 積を pd Čech の cup 積へ送る。

## 方針
外次数零の同型が積を保つことと余単体的な自然性を使う。

## 規約
cup 積の左因子に前面、右因子に後面を使う。

## 使われ方
pd de Rham のコホモロジー積。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham AlgebraicTopology
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

private theorem exteriorZeroEquiv_coe (n : SimplexCategory) (v : ⋀[k]^0 (CopyModule k r n)) :
    (v : ExteriorAlgebra k (CopyModule k r n)) =
      algebraMap k (ExteriorAlgebra k (CopyModule k r n))
        (exteriorPower.zeroEquiv k (CopyModule k r n) v) := by
  let E := exteriorPower.zeroEquiv k (CopyModule k r n)
  obtain ⟨c, rfl⟩ := E.symm.surjective v
  simp [E, exteriorPower.zeroEquiv, ExteriorAlgebra.ιMulti_apply, Algebra.algebraMap_eq_smul_one]

private theorem exteriorZeroEquiv_mul (n : SimplexCategory) (v w : ⋀[k]^0 (CopyModule k r n)) :
    exteriorPower.zeroEquiv k (CopyModule k r n) (exteriorWedge k (CopyModule k r n) 0 0 v w) =
      exteriorPower.zeroEquiv k (CopyModule k r n) v *
        exteriorPower.zeroEquiv k (CopyModule k r n) w := by
  let E := exteriorPower.zeroEquiv k (CopyModule k r n)
  apply E.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  change v.1 * w.1 = _
  conv_rhs => rw [exteriorZeroEquiv_coe k r n, E.apply_symm_apply, map_mul]
  rw [exteriorZeroEquiv_coe k r n v, exteriorZeroEquiv_coe k r n w]

private theorem rowZeroTerm_tmul (n : SimplexCategory) (f : pdTerm p k r n.len)
    (v : ⋀[k]^0 (CopyModule k r n)) :
    rowZeroTerm p k r n (f ⊗ₜ[k] v) = exteriorPower.zeroEquiv k (CopyModule k r n) v • f := by
  simp [rowZeroTerm, TensorProduct.congr_tmul]

set_option backward.isDefEq.respectTransparency false in
private theorem rowZeroTerm_mul (n : SimplexCategory) (x y : (pdRow p k r 0).obj n) :
    rowZeroTerm p k r n (pdWedge p k r n 0 0 x y) =
      rowZeroTerm p k r n x * rowZeroTerm p k r n y := by
  let F := (rowZeroTerm p k r n).toLinearMap
  let W := wedgeTensor p k r n 0 0
  let L := W.compr₂ F
  let R := (LinearMap.mul k (pdTerm p k r n.len)).compl₁₂ F F
  have h : L = R := by
    apply TensorProduct.ext'
    intro f v
    apply TensorProduct.ext'
    intro g w
    change F (W (f ⊗ₜ[k] v) (g ⊗ₜ[k] w)) = F (f ⊗ₜ[k] v) * F (g ⊗ₜ[k] w)
    rw [show W = wedgeTensor p k r n 0 0 from rfl, wedgeTensor, TensorProduct.map₂_apply_tmul,
      TensorProduct.map_tmul, LinearMap.mul_apply']
    erw [rowZeroTerm_tmul, rowZeroTerm_tmul, rowZeroTerm_tmul, exteriorZeroEquiv_mul]
    simp only [Algebra.smul_def, map_mul]
    ac_rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

set_option backward.isDefEq.respectTransparency false in
/-- 外次数零を消す同型は余鎖の cup 積を保つ。 -/
theorem pdDeRhamRowZeroIso_mul (i j : ℕ)
    (x : ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r 0)).X i)
    (y : ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r 0)).X j) :
    (pdDeRhamRowZeroIso p k r).hom.f (i+j) ((pdRowZeroCochainProduct p k r).mul i j x y) =
      (moduleCochainCup k (pdCechRings p k r) (pdCechBase p k r)).mul i j
        ((pdDeRhamRowZeroIso p k r).hom.f i x) ((pdDeRhamRowZeroIso p k r).hom.f j y) := by
  let e := (rowZeroIso p k r ≪≫ coeffIso p k r).hom
  let Y := pdRow p k r 0
  let Z := toModules k (pdCechRings p k r) (pdCechBase p k r)
  change rowZeroTerm p k r ⦋i+j⦌
      (pdWedge p k r ⦋i+j⦌ 0 0 (Y.map (frontFace i j) x) (Y.map (backFace i j) y)) =
    termMul k (pdCechRings p k r) (pdCechBase p k r) ⦋i+j⦌
      (Z.map (frontFace i j) (e.app ⦋i⦌ x)) (Z.map (backFace i j) (e.app ⦋j⦌ y))
  have h₁ := ConcreteCategory.congr_hom (e.naturality (frontFace i j)) x
  have h₂ := ConcreteCategory.congr_hom (e.naturality (backFace i j)) y
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [← h₁, ← h₂]
  exact rowZeroTerm_mul p k r ⦋i+j⦌ _ _

end SerrePositivity.BhattScholze.Prismatic
