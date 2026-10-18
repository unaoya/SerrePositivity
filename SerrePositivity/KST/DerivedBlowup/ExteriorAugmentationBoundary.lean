module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentation
public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeZero

/-!
概要：KST Def3.1 の標準添加射の H⁰ 計算に必要な境界像の同定。
方針：第1外積の元を生成加群から取り出し、収縮を d の値として計算する。
規約：生成加群・微分は任意。正則性は不要。
使われ方：H⁰ と係数環の関係式商の標準比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：次数0項の包含は基底環同型を介した係数写像に等しい。
方針：単位射の次数0成分が同型の逆であることを使う。
規約：KST Def3.1。使われ方：境界像を基底環で計算する。 -/
theorem exteriorCochainInclusion_degree_zero (d : M →ₗ[R] R)
    (z : (exteriorKoszulCochain d).X 0) :
    exteriorCochainInclusion d 0 z =
      algebraMap R (ExteriorAlgebra R M) ((exteriorCochainZeroIso d).hom.hom z) := by
  have h := exteriorKoszulUnit_inclusion d ((exteriorCochainZeroIso d).hom.hom z)
  rw [exteriorKoszulUnit_f_zero] at h
  change exteriorCochainInclusion d 0
    ((exteriorCochainZeroIso d).toLinearEquiv.symm
      ((exteriorCochainZeroIso d).toLinearEquiv z)) = _ at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- 概要：次数−1の微分は生成加群の収縮写像として基底環に写る。
方針：次数0の包含と微分の包含公式を比較し、係数写像の単射性を使う。
規約：KST Def3.1。使われ方：境界像と関係式イデアルの同定。 -/
theorem exteriorCochainZeroIso_d (d : M →ₗ[R] R)
    (z : (exteriorKoszulCochain d).X (-1)) (m : M)
    (hm : ExteriorAlgebra.ι R m = exteriorCochainInclusion d (-1) z) :
    (exteriorCochainZeroIso d).hom.hom (((exteriorKoszulCochain d).d (-1) 0).hom z) =
      d m := by
  apply (ExteriorAlgebra.algebraMap_leftInverse M).injective
  rw [← exteriorCochainInclusion_degree_zero]
  rw [show (0 : ℤ) = -1 + 1 from rfl, exteriorCochainInclusion_d, ← hm,
    CliffordAlgebra.contractLeft_ι]

/-- 概要：次数0境界の基底環での像は d の像に等しい。
方針：第1外積が生成加群の像であることを両方向に使う。
規約：KST Def3.1。使われ方：標準 H⁰ 同型を構成するための商の部分加群。 -/
theorem exteriorBoundary_range (d : M →ₗ[R] R) :
    LinearMap.range ((exteriorCochainZeroIso d).hom.hom.comp
      ((exteriorKoszulCochain d).d (-1) 0).hom) = LinearMap.range d := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz := exteriorCochainInclusion_mem d (-1) z
    change exteriorCochainInclusion d (-1) z ∈
      (LinearMap.range (ExteriorAlgebra.ι R (M := M))) ^ 1 at hz
    rw [pow_one] at hz
    obtain ⟨m, hm⟩ := hz
    exact ⟨m, (exteriorCochainZeroIso_d d z m hm).symm⟩
  · rintro _ ⟨m, rfl⟩
    have hm : ExteriorAlgebra.ι R m ∈ ExteriorAlgebra.exteriorPower R 1 M := by
      change ExteriorAlgebra.ι R m ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 1
      rw [pow_one]
      exact LinearMap.mem_range_self _ m
    let z := (exteriorCochainXIsoNonpos d (-1) (by omega)).inv.hom ⟨_, hm⟩
    refine ⟨z, ?_⟩
    apply exteriorCochainZeroIso_d d z m
    exact (exteriorCochainInclusion_inv d (-1) (by omega) ⟨_, hm⟩).symm

/-- 概要：標準添加の次数0成分は基底環同型に係数構造射を合成したもの。
方針：次数0包含の係数表示と代数準同型の係数保存を使う。
規約：KST Def3.1。使われ方：標準 H⁰ 同型との可換性。 -/
theorem exteriorCochainAugmentationComponent_zero {S : Type u}
    [CommRing S] [Algebra R S] (d : M →ₗ[R] R)
    (z : (exteriorKoszulCochain d).X 0) :
    exteriorCochainAugmentationComponent (S := S) d 0 z =
      algebraMap R S ((exteriorCochainZeroIso d).hom.hom z) := by
  change exteriorAugmentation (S := S) (exteriorCochainInclusion d 0 z) = _
  rw [exteriorCochainInclusion_degree_zero]
  exact (exteriorAugmentation (R := R) (M := M) (S := S)).commutes _

end SerrePositivity.KST.DerivedBlowup
