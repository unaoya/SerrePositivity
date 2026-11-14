module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramCoefficientEZ
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoefficientTensorNaturality
public import SerrePositivity.HomologicalAlgebra.PointwiseExtendComplex

/-!
概要：図式の係数変更後のテンソルを、元の一般係数の負次数正規化テンソルと同定する。
方針：指定係数テンソル同型の自然性と、図式・零延長の交換同型を用いる。
規約：二因子の全射と元の成分包含を保持する。
使われ方：HA 1.2.4、G10 の一般係数の図式 EZ 比較の標的。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {A : Type u} [CommRing A]
variable (φ : simplicialRingCoefficient.{u} →+* A)
variable (C D : J ⥤ SimplicialObject (ModuleCat.{u} ℤ))

/-- 各因子を係数変更してから元の正規化・負次数延長を取る図式。 -/
abbrev negativeMooreCoefficientDiagram (C : J ⥤ SimplicialObject (ModuleCat.{u} ℤ)) :=
  C ⋙ (SimplicialObject.whiskering _ _).obj (integerCoefficientExtension φ) ⋙
    normalizedMooreComplex (ModuleCat A) ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)

/-- 元の一般係数の正規化二因子のテンソル図式。 -/
def negativeEZTargetDiagram : J ⥤ CochainComplex (ModuleCat A) ℤ where
  obj j := (negativeMooreCoefficientDiagram φ C).obj j ⊗ (negativeMooreCoefficientDiagram φ D).obj j
  map f := (negativeMooreCoefficientDiagram φ C).map f ⊗ₘ (negativeMooreCoefficientDiagram φ D).map f
  map_id j := by simp only [CategoryTheory.Functor.map_id, tensorHom_id, id_whiskerRight]
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp, tensorHom_comp_tensorHom]

/-- 同じ係数テンソル比較による全図式の自然同型。 -/
def negativeEZTargetDiagramIso :
    integerEZTargetDiagram C D ⋙ (integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A) ≅ negativeEZTargetDiagram φ C D :=
  NatIso.ofComponents (fun j => negativeMooreTensorCoefficientIso φ (C.obj j) (D.obj j))
    (fun f => negativeMooreTensorCoefficientIso_naturality φ (C.map f) (D.map f))

/-- 図式交換後の延長を、各対象で延長した図式へ戻す指定同型。 -/
def negativeDiagramExchangeIso (K : J ⥤ ChainComplex (ModuleCat A) ℕ) :
    ((functorToComplexOfFunctors J (ModuleCat A) (.down ℕ)).obj K).extend
      ComplexShape.embeddingDownNat ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (K ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) :=
  ((functorComplexExchangeCounitIso J (ModuleCat A) (.up ℤ)).app _).symm ≪≫
  (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).mapIso
    ((pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).app _) ≪≫
  (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).mapIso
    (Functor.isoWhiskerRight ((functorComplexExchangeUnitIso J (ModuleCat A) (.down ℕ)).app K).symm
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)))

/-- 標的を元の一般係数の正規化テンソル図式に戻した指定同値。 -/
def negativeEZDiagramTargetEquiv :
    HomotopyEquiv
      (((functorToComplexOfFunctors J (ModuleCat A) (.down ℕ)).obj
        (coefficientEZSourceDiagram (integerCoefficientExtension φ) C D)).extend ComplexShape.embeddingDownNat)
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj (negativeEZTargetDiagram φ C D)) :=
  (negativeCoefficientEZDiagramEquiv (integerCoefficientExtension φ) C D).trans
    (HomotopyEquiv.ofIso (negativeDiagramExchangeIso
      (integerEZTargetDiagram C D ⋙ (integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)) ≪≫
      (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).mapIso (negativeEZTargetDiagramIso φ C D)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
