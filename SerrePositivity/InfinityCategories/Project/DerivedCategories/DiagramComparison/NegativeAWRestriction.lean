module
public import SerrePositivity.HomologicalAlgebra.MappedNormalizedAWRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient

/-!
概要：raw AWの同じ成分等式を係数移送した負次数AWへ制限する。
方針：指定Moore分裂の制限則と延長項同型の両逆を使う。
規約：元の係数同型と負次数AWを変えない既存構成の合成則。
使われ方：HA 1.2.4、IS-W2 B02の生成元による照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 指定延長項同型で戻した負次数AWの成分は、同じraw成分等式で同定される。 -/
theorem negativeCoefficientAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : ModuleCat A)
    (t : (HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)).X (-(n : ℤ)) ⟶ T)
    (h : ((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).X n ⟶ T)
    (hraw : (integerCoefficientExtension φ).map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex _).obj C)
            ((normalizedMooreComplex _).obj D))).extendXIso ComplexShape.embeddingDownNat
              (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ C D).hom.f (-(n : ℤ)) ≫ t =
      (integerCoefficientExtension φ).map
        ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso (integerCoefficientExtension φ)
          (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeCoefficientAlexanderWhitney φ C D).f (-(n : ℤ)) ≫ t = h := by
  let S := (normalizedMooreComplex (ModuleCat A)).obj
    (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)
  let m := mappedNormalizedAlexanderWhitney (integerCoefficientExtension φ) C D
  have hm := extendMap_f m ComplexShape.embeddingDownNat
    (i := n) (i' := -(n : ℤ)) rfl
  change (S.extendXIso ComplexShape.embeddingDownNat
      (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      ((extendMap m ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫
        (negativeMooreTensorCoefficientIso φ C D).hom.f (-(n : ℤ))) ≫ t = h
  rw [hm]
  simp only [← Category.assoc]
  have hi := (S.extendXIso ComplexShape.embeddingDownNat
    (i := n) (i' := -(n : ℤ)) rfl).inv_hom_id
  rw [hi, Category.id_comp]
  simp only [Category.assoc]
  exact mappedNormalizedAlexanderWhitney_f_eq_of_raw (integerCoefficientExtension φ)
    C D n T _ h (by simpa only [Category.assoc] using hraw)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
