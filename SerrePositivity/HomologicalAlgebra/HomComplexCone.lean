module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # 写像錐を始域とするHom複体の二成分表示 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CochainComplex.HomComplex
variable (R : Type u) [CommRing R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

/-- 錐を始域とする次数nのcochainは、m+1=nの二成分で一意に表される。 -/
def mappingConeSourceCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (m n : ℤ) (h : m + 1 = n) :
    Cochain (CochainComplex.mappingCone φ) K n ≃ₗ[R]
      Cochain F K m × Cochain G K n where
  toFun x := ⟨(CochainComplex.mappingCone.inl φ).comp x (by omega),
    (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp x (zero_add n)⟩
  invFun x := CochainComplex.mappingCone.descCochain φ x.1 x.2 h
  left_inv x := by
    rw [CochainComplex.mappingCone.ext_cochain_from_iff φ m n h]
    exact ⟨by simp, by simp⟩
  right_inv x := by simp
  map_add' x y := by simp only [Cochain.comp_add]; rfl
  map_smul' r x := by simp only [Cochain.comp_smul]; rfl

/-- 二成分から組み立てたcochainの微分と、その符号付き前合成。 -/
theorem mappingConeSourceCochainEquiv_symm_δ
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (α : Cochain F K m) (β : Cochain G K n) :
    δ n p ((mappingConeSourceCochainEquiv R φ K m n h).symm (α, β)) =
      (mappingConeSourceCochainEquiv R φ K n p h').symm
        (δ m n α + p.negOnePow • (Cochain.ofHom φ).comp β (zero_add n), δ n p β) := by
  exact CochainComplex.mappingCone.δ_descCochain φ α β h p h'

end SerrePositivity
