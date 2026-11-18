module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexCochainContraction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# 正規化単体をテンソルした非有界複体の収縮

概要：X⊗N(Δⁿ) の元の augmentation は任意 X で鎖ホモトピー同値。
方針：同じ単体収縮の二つのホモトピーをテンソルし、右単位子で終域を同定する。
規約：flatness や cofibrancy を仮定しない。
使われ方：正規化単体テンソルの homotopically constant 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def normalizedSimplexTensorContraction (X : Complex A) (n : SimplexCategory) :
    HomotopyEquiv ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).obj n) X := by
  let h := _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n
  let h' : HomotopyEquiv (X ⊗ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))
      (X ⊗ 𝟙_ (Complex A)) := {
    hom := 𝟙 X ⊗ₘ h.hom
    inv := 𝟙 X ⊗ₘ h.inv
    homotopyHomInvId := by
      have hh := mapBifunctorMapHomotopy₂ (𝟙 X) h.homotopyHomInvId
        (curriedTensor (ModuleCat A)) (.up ℤ)
      change Homotopy (𝟙 X ⊗ₘ (h.hom ≫ h.inv)) (𝟙 X ⊗ₘ 𝟙 _) at hh
      rw [tensorHom_comp_tensorHom, Category.id_comp]
      simpa only [tensorHom_id, id_whiskerRight] using hh
    homotopyInvHomId := by
      have hh := mapBifunctorMapHomotopy₂ (𝟙 X) h.homotopyInvHomId
        (curriedTensor (ModuleCat A)) (.up ℤ)
      change Homotopy (𝟙 X ⊗ₘ (h.inv ≫ h.hom)) (𝟙 X ⊗ₘ 𝟙 _) at hh
      rw [tensorHom_comp_tensorHom, Category.id_comp]
      simpa only [tensorHom_id, id_whiskerRight] using hh }
  exact h'.trans (HomotopyEquiv.ofIso (ρ_ X))

lemma normalizedSimplexTensorAugmentation_quasiIso (X : Complex A) (n : SimplexCategory) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorContraction A X n).hom) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorContraction A X n).quasiIso_hom

end SerrePositivity.ComplexLimits
