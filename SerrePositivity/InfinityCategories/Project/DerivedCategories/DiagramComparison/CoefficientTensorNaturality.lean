module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
public import SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChangeNaturality

/-!
概要：整数係数移送と Moore 比較を重ねた負次数テンソル同型の自然性。
方針：既存の各比較の自然性を同じ射のまま前後合成する。
規約：任意の宇宙の二つの単体的整数加群の全射を扱う。
使われ方：HA 1.2.4、G10 の全単体パラメータへの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 整数係数移送と底変換を合成した指定同型は元の二つの鎖写像に自然。 -/
@[reassoc]
theorem integerNegativeTensorBaseChangeIso_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    extendMap (((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map
        (chainIntegerTensorMap f g)) ComplexShape.embeddingDownNat ≫
        (integerNegativeTensorBaseChangeIso K' L' φ).hom =
      (integerNegativeTensorBaseChangeIso K L φ).hom ≫ HomologicalComplex.tensorHom
        (extendMap (((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map f)
          ComplexShape.embeddingDownNat)
        (extendMap (((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map g)
          ComplexShape.embeddingDownNat) := by
  let G := (ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)
  let T := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have h0 := congrArg (fun t => T.map (G.map t)) (integerCoefficientChainTensorIso_naturality f g)
  simp only [Functor.map_comp] at h0
  have h1 := negativeTensorBaseChangeIso_naturality φ
    ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map f)
    ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map g)
  dsimp only [integerNegativeTensorBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [reassoc_of% h0, h1]
  rfl

/-- 最後に元の Moore 正規化へ戻すテンソル同型も全単体的射に自然。 -/
@[reassoc]
theorem negativeMooreTensorCoefficientIso_naturality
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    extendMap (((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).map
        (chainIntegerTensorMap ((normalizedMooreComplex _).map f)
          ((normalizedMooreComplex _).map g))) ComplexShape.embeddingDownNat ≫
        (negativeMooreTensorCoefficientIso φ C' D').hom =
      (negativeMooreTensorCoefficientIso φ C D).hom ≫ HomologicalComplex.tensorHom
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight f
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat)
        (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight g
          (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat) := by
  let F := integerCoefficientExtension φ
  let T := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have h0 := integerNegativeTensorBaseChangeIso_naturality φ
    ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)
  have hf := congrArg T.map (normalizedMooreMapHom_naturality F f)
  have hg := congrArg T.map (normalizedMooreMapHom_naturality F g)
  simp only [Functor.map_comp] at hf hg
  dsimp only [negativeMooreTensorCoefficientIso, Iso.trans_hom, tensorIso_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [reassoc_of% h0]
  congr 1
  erw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg₂ (fun a b => a ⊗ₘ b) hf hg

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
