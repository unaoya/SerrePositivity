module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexContractionNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorContraction

/-!
# 正規化単体テンソルの全 augmentation と全作用素の擬同型性

概要：同じ X⊗N(Δⁿ) から X への全自然 augmentation は各次数で擬同型。
方針：元の鎖収縮の順方向の自然性をテンソルし、二対三で全作用素へ移す。
規約：任意の非有界複体に適用し、flatness や cofibrancy を仮定しない。
使われ方：同じ正規化単体テンソルの frame 比較。
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

def normalizedSimplexTensorAugmentation (X : Complex A) :
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X ⟶ (Functor.const SimplexCategory).obj X where
  app n := (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorContraction A X n).hom
  naturality {n m} f := by
    change (𝟙 X ⊗ₘ (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map f)) ≫
      ((𝟙 X ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A m).hom) ≫ (ρ_ X).hom) =
        ((𝟙 X ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ X).hom) ≫ 𝟙 X
    rw [Category.comp_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
      _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction_naturality]

lemma normalizedSimplexTensor_map_quasiIso (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f) := by
  have hm : QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app m) :=
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation_quasiIso A X m
  have hn : QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n) :=
    _root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation_quasiIso A X n
  have h := (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).naturality f
  change _ = (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app n ≫ 𝟙 X at h
  erw [Category.comp_id] at h
  have : QuasiIso ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensor A X).map f ≫
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app m) := by
    rw [h]
    exact hn
  exact quasiIso_of_comp_right _ ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexTensorAugmentation A X).app m)

end SerrePositivity.ComplexLimits
