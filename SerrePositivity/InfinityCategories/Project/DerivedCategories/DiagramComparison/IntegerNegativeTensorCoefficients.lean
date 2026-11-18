module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
public import SerrePositivity.HomologicalAlgebra.MapExtendComponents

/-!
概要：指定された整数テンソルの係数移送を各直和成分で計算する。
方針：係数テンソル・零延長・負次数比較の既存の成分公式を合成する。
規約：元の比較同型と直和包含を保持する。IS-W2の前提計算枠3。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
variable (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ)
local notation "F" => integerCoefficientExtension φ
local notation "Kφ" => Functor.obj (Functor.mapHomologicalComplex (integerCoefficientExtension φ) (ComplexShape.down ℕ)) K
local notation "Lφ" => Functor.obj (Functor.mapHomologicalComplex (integerCoefficientExtension φ) (ComplexShape.down ℕ)) L

/-- 指定係数移送は元の斉次包含を対応する負次数の包含へ送る。 -/
theorem integerNegativeTensorBaseChangeIso_ι (i j n : ℕ) (h : i + j = n) :
    (F).map (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫
      ((((F).mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor K L)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (integerNegativeTensorBaseChangeIso K L φ).hom.f (-(n : ℤ)) =
    (ModuleCat.extendScalars φ).map (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
        (integerCoefficientModuleFunctor.obj (K.X i))
        (integerCoefficientModuleFunctor.obj (L.X j)) ≫
      (((Kφ).extendXIso ComplexShape.embeddingDownNat (i := i) (i' := -(i : ℤ)) rfl).inv ⊗ₘ
        ((Lφ).extendXIso ComplexShape.embeddingDownNat (i := j) (i' := -(j : ℤ)) rfl).inv) ≫
      ιTensorObj ((Kφ).extend ComplexShape.embeddingDownNat)
        ((Lφ).extend ComplexShape.embeddingDownNat) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
        (by omega) := by
  dsimp only [integerNegativeTensorBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [comp_f]
  change _ ≫ _ ≫ (extendMap _ ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  erw [extendMap_f _ _ (i := n) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.mapHomologicalComplex_map_f]
  change (ModuleCat.extendScalars φ).map
      (integerCoefficientModuleFunctor.map (ιMapBifunctor K L integerTensorBifunctor
        (.down ℕ) i j n h)) ≫ (ModuleCat.extendScalars φ).map
      (integerCoefficientTensorXIso K L n).hom ≫ _ = _
  rw [← Functor.map_comp_assoc, map_ι_integerCoefficientTensorXIso, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  dsimp only [negativeTensorBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_hom]
  simp only [comp_f, Functor.mapHomologicalComplex_map_f]
  erw [mapExtendIso_inv_f _ _ _ (i := n) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    _root_.SerrePositivity.NegativeTensor.comparison_hom_f_neg, Functor.map_comp]
  simp only [← Functor.map_comp_assoc]
  simp only [_root_.SerrePositivity.NegativeTensor.xIso, Iso.inv_hom_id_assoc]
  rw [_root_.SerrePositivity.NegativeTensor.ι_degreeMap, Functor.map_comp]
  simp only [Category.assoc]
  change _ ≫ (ModuleCat.extendScalars φ).map (ιTensorObj _ _ _ _ _ _) ≫
    (cochainTensorBaseChangeXIso φ _ _ _).hom ≫ _ = _
  rw [map_ι_cochainTensorBaseChangeXIso_assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [DifferentialGraded.ι_tensorHom]
  erw [← Category.assoc (_ ⊗ₘ _) (_ ⊗ₘ _) _,
    MonoidalCategory.tensorHom_comp_tensorHom]
  congr 2
  congr 1
  · apply (cancel_mono ((Kφ).extendXIso ComplexShape.embeddingDownNat
      (i := i) (i' := -(i : ℤ)) rfl).hom).1
    erw [Category.assoc, mapExtendIso_hom_f]
    simp only [_root_.SerrePositivity.NegativeTensor.xIso, ← Functor.map_comp,
      Iso.inv_hom_id]
    exact (ModuleCat.extendScalars φ).map_id _
  · apply (cancel_mono ((Lφ).extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := -(j : ℤ)) rfl).hom).1
    erw [Category.assoc, mapExtendIso_hom_f]
    simp only [_root_.SerrePositivity.NegativeTensor.xIso, ← Functor.map_comp,
      Iso.inv_hom_id]
    exact (ModuleCat.extendScalars φ).map_id _


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
