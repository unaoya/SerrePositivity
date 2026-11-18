module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterRightUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentationValues
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsCoefficientDegrees
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerNegativeTensorCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedAWRightAugmentationCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductFrameCoaction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardParameterAugmentation
/-!
概要：指定AWの最後の切断の右余単位則。
方針：係数移送の純テンソルを評価する。規約：IS-W2 A05aの証明の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial TensorProduct
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 指定AWの最後の切断の右余単位則。 -/
theorem freeProductAlexanderWhitney_last_cut_right_augmentation
    (A : Type u) [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
    (Z : SSet.{u}) (n : SimplexCategory) (k : ℕ) :
  let Y := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)
  let F := integerCoefficientExtension φ
  let NC := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Z)
  let ND := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
  let e0 := Functor.isoWhiskerRight (linearizedTensorIso Z Y) F ≪≫
    integerCoefficientSimplicialFreeIso φ (Z ⊗ Y)
  F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
      k (Fin.last k) ≫
      (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace Z))
        (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f k) ≫
    (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).extendXIso
      ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv ≫
    ((negativeMooreTensorCoefficientIso φ (linearizedSpace Z) (linearizedSpace Y)).hom ≫
      (tensorIso (integerCoefficientFreeChainsIso φ Z)
        (integerCoefficientFreeChainsIso φ Y)).hom ≫
      (𝟙 _ ⊗ₘ (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom) ≫
      (ρ_ (freeNegativeChains (A := A) Z)).hom).f (-(k : ℤ)) =
    e0.hom.app (Opposite.op ⦋k⦌) ≫
      (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
      (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (Z ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv := by
  let Y := (SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n)
  let F := integerCoefficientExtension φ
  let T := simplicialIntegerTensor (linearizedSpace Z) (linearizedSpace Y)
  let ε : freeNegativeChains (A := A) Y ⟶ 𝟙_ (CochainComplex (ModuleCat A) ℤ) :=
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom
  let e0 := Functor.isoWhiskerRight (linearizedTensorIso Z Y) F ≪≫
    integerCoefficientSimplicialFreeIso φ (Z ⊗ Y)
  let γ := (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace Z))
    (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f k
  let NC := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Z)
  let ND := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
  let out : ((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).X k ⟶
      (freeNegativeChains (A := A) Z).X (-(k : ℤ)) :=
    (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor NC ND)).extendXIso
      ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv ≫
    ((negativeMooreTensorCoefficientIso φ (linearizedSpace Z) (linearizedSpace Y)).hom ≫
      (tensorIso (integerCoefficientFreeChainsIso φ Z)
        (integerCoefficientFreeChainsIso φ Y)).hom ≫
      (𝟙 _ ⊗ₘ ε) ≫
      (ρ_ (freeNegativeChains (A := A) Z)).hom).f (-(k : ℤ))
  change F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
    k (Fin.last k) ≫ γ) ≫ out =
  e0.hom.app (Opposite.op ⦋k⦌) ≫
    (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
    (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k ≫
    (((normalizedMooreComplex (ModuleCat A)).obj (Z ⋙ ModuleCat.free A)).extendXIso
      ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv
  let adj := simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)
  apply (adj.homEquiv _ _).injective
  apply integerTensor_hom_ext
  intro z y
  letI := φ.toAlgebra
  letI : Module simplicialRingCoefficient A := φ.toAlgebra.toModule
  let v : F.obj (T.obj (Opposite.op ⦋k⦌)) :=
    coefficientUnit φ (T.obj (Opposite.op ⦋k⦌)) (integerGenerator z ⊗ₜ[ℤ] integerGenerator y)
  change (F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
    k (Fin.last k) ≫ γ) ≫ out) v =
    (e0.hom.app (Opposite.op ⦋k⦌) ≫
      (ModuleCat.free A).map ((fst Z Y).app (Opposite.op ⦋k⦌)) ≫
      (PInftyToNormalizedMooreComplex (Z ⋙ ModuleCat.free A)).f k ≫
      (((normalizedMooreComplex (ModuleCat A)).obj (Z ⋙ ModuleCat.free A)).extendXIso
        ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl).inv) v
  have he0 : e0.hom.app (Opposite.op ⦋k⦌) v = ModuleCat.freeMk (z, y) := by
    change (integerCoefficientFreeIso φ).hom.app _
      ((1 : A) ⊗ₜ[simplicialRingCoefficient]
        ((integerTensorIso _ _).hom (integerGenerator z ⊗ₜ[ℤ] integerGenerator y))) = _
    rw [integerTensorIso_generator]
    exact integerCoefficientFreeIso_generator φ _ (z, y)
  simp only [ModuleCat.comp_apply, he0]
  erw [ModuleCat.free_map_apply]
  change (F.map (alexanderWhitneySummand (linearizedSpace Z) (linearizedSpace Y)
    k (Fin.last k) ≫ γ) ≫ out) v = _
  dsimp only [alexanderWhitneySummand, γ]
  rw [Category.assoc, ι_chainIntegerTensorMap]
  let zf := Z.map (awFront k (Fin.last k)).op z
  let yb := Y.map (awBack k (Fin.last k)).op y
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  have hv := coefficientUnit_tensorMap φ
    ((linearizedSpace Z).map (awFront k (Fin.last k)).op)
    ((linearizedSpace Y).map (awBack k (Fin.last k)).op)
    (integerGenerator z) (integerGenerator y)
  have hzg : ((linearizedSpace Z).map (awFront k (Fin.last k)).op) (integerGenerator z) =
      integerGenerator zf := integerLinearization_map_generator _ _
  have hyg : ((linearizedSpace Y).map (awBack k (Fin.last k)).op) (integerGenerator y) =
      integerGenerator yb := integerLinearization_map_generator _ _
  rw [hzg, hyg] at hv
  refine (congrArg (fun t => out (F.map
    (ιMapBifunctor NC ND integerTensorBifunctor (.down ℕ) k (k - k) k
      (awDegrees k (Fin.last k)))
    (F.map (integerTensorMap
      ((PInftyToNormalizedMooreComplex (linearizedSpace Z)).f k)
      ((PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (k - k))) t))) hv).trans ?_
  have hw := coefficientUnit_tensorMap φ
    ((PInftyToNormalizedMooreComplex (linearizedSpace Z)).f k)
    ((PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (k - k))
    (integerGenerator zf) (integerGenerator yb)
  refine (congrArg (fun t => out (F.map
    (ιMapBifunctor NC ND integerTensorBifunctor (.down ℕ) k (k - k) k
      (awDegrees k (Fin.last k))) t)) hw).trans ?_
  change (F.map (ιMapBifunctor NC ND integerTensorBifunctor (.down ℕ)
    k (k - k) k (awDegrees k (Fin.last k))) ≫ out)
      (coefficientUnit φ (integerTensor (NC.X k) (ND.X (k - k)))
        (((PInftyToNormalizedMooreComplex (linearizedSpace Z)).f k (integerGenerator zf)) ⊗ₜ[ℤ]
          ((PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (k - k) (integerGenerator yb)))) = _
  dsimp only [out, negativeMooreTensorCoefficientIso, Iso.trans_hom,
    tensorIso_hom, Functor.mapIso_hom]
  simp only [comp_f, Category.assoc]
  erw [reassoc_of% (integerNegativeTensorBaseChangeIso_ι φ NC ND
    k (k - k) k (awDegrees k (Fin.last k)))]
  rw [DifferentialGraded.ι_tensorHom_assoc,
    DifferentialGraded.ι_tensorHom_assoc, DifferentialGraded.ι_tensorHom_assoc]
  simp only [ModuleCat.comp_apply]
  have ht := coefficientUnit_tensorComparison φ (NC.X k) (ND.X (k - k))
    ((PInftyToNormalizedMooreComplex (linearizedSpace Z)).f k (integerGenerator zf))
    ((PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (k - k) (integerGenerator yb))
  erw [ht, ModuleCat.MonoidalCategory.tensorHom_tmul]
  dsimp only [Prod.fst, Prod.snd, id_f]
  have hz := freeChainsCoefficient_generator_value φ Z k zf
  have hy := freeChainsCoefficient_generator_value φ Y (k - k) yb
  erw [hz, hy]
  have hf : awFront k (Fin.last k) = 𝟙 _ := by
    apply SimplexCategory.Hom.ext
    ext i
    rfl
  have hzfid : zf = z := by
    dsimp only [zf]
    rw [hf, op_id]
    exact ConcreteCategory.congr_hom (Z.map_id _) z
  have hfst : ((fst Z Y).app (Opposite.op ⦋k⦌)) (z, y) = z := rfl
  erw [hzfid, hfst]
  exact standardParameter_right_unit A n (freeNegativeChains (A := A) Z)
    (k - k) (Nat.sub_self k) (-(k : ℤ)) yb _


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
