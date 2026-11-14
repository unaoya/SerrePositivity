module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientUnitNaturality

/-!
概要：係数移送した積の自由化比較は同じMoore射影と負次数行を保つ。
方針：既存Moore係数比較の射影自然性と積の自由化同型を合成する。
規約：元の整数テンソル・積の自由化・係数比較を保持する既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02のraw AWから正規化AWへの制限。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 同じ積の自由化比較は、係数移送した元のMoore射影と可換。 -/
theorem productChainsCoefficient_projection (X Y : SSet.{u}) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    (F.mapHomologicalComplex (.down ℕ)).map (PInftyToNormalizedMooreComplex S) ≫
      normalizedMooreMapHom F S ≫ (normalizedMooreComplex (ModuleCat A)).map e.hom =
      (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app S ≫
        (alternatingFaceMapComplex (ModuleCat A)).map e.hom ≫
          PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A) := by
  dsimp only
  rw [normalizedMooreMapHom_projection_assoc]
  erw [← PInftyToNormalizedMooreComplex_naturality]
  rfl

/-- 同じ積の係数射影比較を元の負次数延長の項同型で表した成分式。 -/
theorem productChainsCoefficient_degree (X Y : SSet.{u}) (r : ℕ) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    F.map ((PInftyToNormalizedMooreComplex S).f r) ≫ (normalizedMooreMapHom F S).f r ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv ≫
      (integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)) =
      e.hom.app (Opposite.op ⦋r⦌) ≫
        (PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)).f r ≫
        (((normalizedMooreComplex (ModuleCat A)).obj ((X ⊗ Y) ⋙ ModuleCat.free A)).extendXIso
          ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv := by
  dsimp only [integerCoefficientProductChainsIso, Functor.mapIso_hom,
    ComplexShape.Embedding.extendFunctor]
  erw [extendMap_f _ _ (i := r) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  let F := integerCoefficientExtension φ
  let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
  let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
    integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
  have h := congrArg (fun f => HomologicalComplex.Hom.f f r)
    (productChainsCoefficient_projection φ X Y)
  change F.map ((PInftyToNormalizedMooreComplex S).f r) ≫
      (normalizedMooreMapHom F S).f r ≫ ((normalizedMooreComplex (ModuleCat A)).map e.hom).f r =
    𝟙 _ ≫ e.hom.app (Opposite.op ⦋r⦌) ≫
      (PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)).f r at h
  simp only [Category.id_comp] at h
  erw [reassoc_of% h]

/-- 同じ積の単体的係数比較は二つの整数生成元を元の積の自由生成元に送る。 -/
theorem productChainsCoefficient_simplicial_generator (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let e := Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
      integerCoefficientSimplicialFreeIso φ (X ⊗ Y)
    e.hom.app (Opposite.op ⦋r⦌)
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
          (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) = ModuleCat.freeMk (x, y) := by
  dsimp only
  change (integerCoefficientFreeIso φ).hom.app
      (X.obj (Opposite.op ⦋r⦌) × Y.obj (Opposite.op ⦋r⦌))
    ((integerCoefficientExtension φ).map
      (integerTensorIso (X.obj (Opposite.op ⦋r⦌)) (Y.obj (Opposite.op ⦋r⦌))).hom
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
          (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))) = _
  have hu := coefficientUnit_map_value φ
    (integerTensorIso (X.obj (Opposite.op ⦋r⦌)) (Y.obj (Opposite.op ⦋r⦌))).hom
      (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)
  have hg := congrArg (fun t => coefficientUnit φ
    (integerLinearization.obj (X.obj (Opposite.op ⦋r⦌) × Y.obj (Opposite.op ⦋r⦌))) t)
      (integerTensorIso_generator (X.obj (Opposite.op ⦋r⦌))
        (Y.obj (Opposite.op ⦋r⦌)) x y)
  have hv := congrArg (fun t => (integerCoefficientFreeIso φ).hom.app
    (X.obj (Opposite.op ⦋r⦌) × Y.obj (Opposite.op ⦋r⦌)) t) (hu.trans hg)
  exact hv.trans (integerCoefficientFreeIso_generator φ _ (x, y))

/-- 指定積係数比較は、同じMoore射影の生成元を元の負次数の積の自由生成元に送る。 -/
theorem productChainsCoefficient_generator_value (X Y : SSet.{u}) (r : ℕ)
    (x : X.obj (Opposite.op ⦋r⦌)) (y : Y.obj (Opposite.op ⦋r⦌)) :
    let F := integerCoefficientExtension φ
    let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
    ((integerCoefficientProductChainsIso φ X Y).hom.f (-(r : ℤ)))
      ((((normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)).extendXIso
        ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
          ((normalizedMooreMapHom F S).f r
            (F.map ((PInftyToNormalizedMooreComplex S).f r)
              (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
                ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
                  (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))))) =
      freeNegativeGenerator (X ⊗ Y) r (x, y) := by
  dsimp only
  have h := congrArg (fun t => t
    (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋r⦌))
      ((linearizedSpace Y).obj (Opposite.op ⦋r⦌)))
        (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)))
    (productChainsCoefficient_degree φ X Y r)
  simp only [comp_f, ModuleCat.comp_apply] at h
  have he := congrArg (fun t =>
    (((normalizedMooreComplex (ModuleCat A)).obj ((X ⊗ Y) ⋙ ModuleCat.free A)).extendXIso
      ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) rfl).inv
      ((PInftyToNormalizedMooreComplex ((X ⊗ Y) ⋙ ModuleCat.free A)).f r t))
        (productChainsCoefficient_simplicial_generator φ X Y r x y)
  exact h.trans he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
