module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDifferential
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDifferential
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamSubstitutionDegreeZero
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegreeInclusion

/-!
# 完備分冪形式の写像を係数上で比較する

## 概要
微分を保ち、総外積上の代数射から来る次数別の写像は、次数 0 で決まる。

## 方針
外積代数の生成元は頂点変数の微分であり、次数 0 の一致から生成元上の一致を得る。

## 規約
余単体次数と有限多項式の変数の数は、始域と終域でそれぞれ固定する。

## 使われ方
多項式代入の余面・余退化との可換性および合成則。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open SerrePositivity.KST.DerivedBlowup
open scoped TensorProduct Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [CommRing k] (p : ℕ) (Q : Poly k) (s m n : ℕ)

local notation "SourceRing" => pdTerm p k Q.n n
local notation "TargetRing" => pdTerm p k s m
local notation "SourceCopy" => ((Fin Q.n × Fin (n + 1)) →₀ k)
local notation "TargetCopy" => ((Fin s × Fin (m + 1)) →₀ k)
local notation "Fs" j => rowModule (k := k) p n Q.n j
local notation "Ft" j => rowModule (k := k) p m s j
local notation "Ds" => pdVerticalD p k Q.n ⦋n⦌
local notation "Dt" => pdVerticalD p k s ⦋m⦌

/-- 各外次数を総外積へ入れる。 -/
def rowFormsInclusion (r a i : ℕ) (x : (pdRow p k r i).obj ⦋a⦌) :
    pdTerm p k r a ⊗[k] ExteriorAlgebra k ((Fin r × Fin (a + 1)) →₀ k) :=
  exteriorBaseChangeDegreeInclusion i x

private theorem exterior_ext
    (f g : (i : ℕ) → (Fs i) ⟶ (Ft i))
    (fE gE : SourceRing ⊗[k] ExteriorAlgebra k SourceCopy →ₐ[k]
      TargetRing ⊗[k] ExteriorAlgebra k TargetCopy)
    (hf : ∀ i (x : Fs i), exteriorBaseChangeDegreeInclusion i (f i x) =
      fE (exteriorBaseChangeDegreeInclusion i x))
    (hg : ∀ i (x : Fs i), exteriorBaseChangeDegreeInclusion i (g i x) =
      gE (exteriorBaseChangeDegreeInclusion i x))
    (hfd : ∀ i, f i ≫ Dt i = Ds i ≫ f (i + 1))
    (hgd : ∀ i, g i ≫ Dt i = Ds i ≫ g (i + 1))
    (h0 : f 0 = g 0) : fE = gE := by
  apply Algebra.TensorProduct.ext
  · ext x
    have h := ConcreteCategory.congr_hom h0
      (x ⊗ₜ[k] (exteriorPower.zeroEquiv k SourceCopy).symm 1)
    have h' := (hf 0 _).symm.trans ((congrArg (exteriorBaseChangeDegreeInclusion 0) h).trans (hg 0 _))
    change fE (x ⊗ₜ[k] ((exteriorPower.zeroEquiv k SourceCopy).symm 1).val) =
      gE (x ⊗ₜ[k] ((exteriorPower.zeroEquiv k SourceCopy).symm 1).val) at h'
    change fE (x ⊗ₜ[k] 1) = gE (x ⊗ₜ[k] 1)
    simpa only [exteriorZero_one] using h'
  · apply ExteriorAlgebra.hom_ext
    let a := (fE.comp Algebra.TensorProduct.includeRight).toLinearMap.comp (ExteriorAlgebra.ι k)
    let b := (gE.comp Algebra.TensorProduct.includeRight).toLinearMap.comp (ExteriorAlgebra.ι k)
    change a = b
    apply (Finsupp.basisSingleOne (R := k)).ext
    rintro ⟨j,i⟩
    let U := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k Q.n n))
    let z : Fs 0 := U (copy k Q.n ⦋n⦌ j i) ⊗ₜ[k] (exteriorPower.zeroEquiv k SourceCopy).symm 1
    have hd : f 1 (Ds 0 z) = g 1 (Ds 0 z) := by
      have hf' := ConcreteCategory.congr_hom (hfd 0) z
      have hg' := ConcreteCategory.congr_hom (hgd 0) z
      simp only [ConcreteCategory.comp_apply] at hf' hg'
      rw [← hf', ← hg', h0]
    have h := (hf 1 _).symm.trans ((congrArg (exteriorBaseChangeDegreeInclusion 1) hd).trans (hg 1 _))
    rw [show Ds 0 z = _ from d_vertex p n j i] at h
    change fE ((1 : SourceRing) ⊗ₜ[k]
      ((exteriorPower.oneEquiv k SourceCopy).symm (Finsupp.single (j,i) 1)).val) =
      gE ((1 : SourceRing) ⊗ₜ[k]
        ((exteriorPower.oneEquiv k SourceCopy).symm (Finsupp.single (j,i) 1)).val) at h
    simpa [a, b, exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti,
      ExteriorAlgebra.ιMulti_apply] using h

/-- 係数と微分を保つ総外積の写像は、次数 0 の写像から一意に決まる。 -/
theorem rowForms_ext
    (f g : (i : ℕ) → (pdRow p k Q.n i).obj ⦋n⦌ ⟶ (pdRow p k s i).obj ⦋m⦌)
    (fE gE : SourceRing ⊗[k] ExteriorAlgebra k SourceCopy →ₐ[k]
      TargetRing ⊗[k] ExteriorAlgebra k TargetCopy)
    (hf : ∀ i (x : (pdRow p k Q.n i).obj ⦋n⦌),
      rowFormsInclusion (k := k) p s m i (f i x) =
        fE (rowFormsInclusion (k := k) p Q.n n i x))
    (hg : ∀ i (x : (pdRow p k Q.n i).obj ⦋n⦌),
      rowFormsInclusion (k := k) p s m i (g i x) =
        gE (rowFormsInclusion (k := k) p Q.n n i x))
    (hfd : ∀ i, f i ≫ Dt i = Ds i ≫ f (i + 1))
    (hgd : ∀ i, g i ≫ Dt i = Ds i ≫ g (i + 1))
    (h0 : f 0 = g 0) (i : ℕ) : f i = g i := by
  have h := exterior_ext p Q s m n f g fE gE hf hg hfd hgd h0
  apply ModuleCat.hom_ext
  ext x
  apply (show Function.Injective (rowFormsInclusion (k := k) p s m i) by
    unfold rowFormsInclusion
    exact exteriorBaseChangeDegreeInclusion_injective (R := k) (S := TargetRing)
      (M := TargetCopy) i)
  change rowFormsInclusion (k := k) p s m i (f i x) =
    rowFormsInclusion (k := k) p s m i (g i x)
  rw [hf, hg, h]

end SerrePositivity.BhattScholze.Prismatic.PDRawPolynomialSubstitution
