module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexContractionNaturality
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorContraction

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def normalizedSimplexTensorAugmentation (X : Complex A) :
    normalizedSimplexTensor A X ⟶ (Functor.const SimplexCategory).obj X where
  app n := (normalizedSimplexTensorContraction A X n).hom
  naturality {n m} f := by
    change (𝟙 X ⊗ₘ (BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map f)) ≫
      ((𝟙 X ⊗ₘ (normalizedSimplexCochainContraction A m).hom) ≫ (ρ_ X).hom) =
        ((𝟙 X ⊗ₘ (normalizedSimplexCochainContraction A n).hom) ≫ (ρ_ X).hom) ≫ 𝟙 X
    rw [Category.comp_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
      normalizedSimplexCochainContraction_naturality]

lemma normalizedSimplexTensor_map_quasiIso (X : Complex A)
    {n m : SimplexCategory} (f : n ⟶ m) :
    QuasiIso ((normalizedSimplexTensor A X).map f) := by
  have hm : QuasiIso ((normalizedSimplexTensorAugmentation A X).app m) :=
    normalizedSimplexTensorAugmentation_quasiIso A X m
  have hn : QuasiIso ((normalizedSimplexTensorAugmentation A X).app n) :=
    normalizedSimplexTensorAugmentation_quasiIso A X n
  have h := (normalizedSimplexTensorAugmentation A X).naturality f
  change _ = (normalizedSimplexTensorAugmentation A X).app n ≫ 𝟙 X at h
  erw [Category.comp_id] at h
  have : QuasiIso ((normalizedSimplexTensor A X).map f ≫
      (normalizedSimplexTensorAugmentation A X).app m) := by
    rw [h]
    exact hn
  exact quasiIso_of_comp_right _ ((normalizedSimplexTensorAugmentation A X).app m)

end SerrePositivity.EInfinity.ComplexLimits
