module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductEZ
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficientNaturality

/-!
概要：指定自由化比較と積比較を元の単体的集合の全射に自然な形で照合する。
方針：自由化の全自然同型と整数テンソル同型を正規化・延長関手で運ぶ。
規約：前段で固定した同型を保持し、点ごとの同型の選び直しをしない。
使われ方：HA 1.2.4、G10 の自由積 EZ 比較の全パラメータ自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 元の自由正規化鎖の射。 -/
abbrev freeNegativeChainsMap {X Y : SSet.{u}} (f : X ⟶ Y) :=
  extendMap ((normalizedMooreComplex (ModuleCat A)).map (Functor.whiskerRight f
    (ModuleCat.free A))) ComplexShape.embeddingDownNat

/-- 単体的自由化比較は単体的集合の全射に自然。 -/
theorem integerCoefficientSimplicialFreeIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    Functor.whiskerRight (linearizedSpaceMap f) (integerCoefficientExtension φ) ≫
        (integerCoefficientSimplicialFreeIso φ Y).hom =
      (integerCoefficientSimplicialFreeIso φ X).hom ≫ Functor.whiskerRight f (ModuleCat.free A) := by
  apply NatTrans.ext
  funext n
  exact (integerCoefficientFreeIso φ).hom.naturality (f.app n)

/-- 正規化・負次数延長後も同じ自由化比較は自然。 -/
@[reassoc]
theorem integerCoefficientFreeChainsIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
        (linearizedSpaceMap f) (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat ≫
        (integerCoefficientFreeChainsIso φ Y).hom =
      (integerCoefficientFreeChainsIso φ X).hom ≫ freeNegativeChainsMap (A := A) f := by
  let T := normalizedMooreComplex (ModuleCat A) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have h := congrArg T.map (integerCoefficientSimplicialFreeIso_naturality φ f)
  simp only [Functor.map_comp] at h
  exact h

/-- 積の係数比較も二つの単体的集合の射に自然。 -/
@[reassoc]
theorem integerCoefficientProductChainsIso_naturality
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
        (simplicialIntegerTensorMap (linearizedSpaceMap f) (linearizedSpaceMap g))
        (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat ≫
        (integerCoefficientProductChainsIso φ X' Y').hom =
      (integerCoefficientProductChainsIso φ X Y).hom ≫ freeNegativeChainsMap (A := A) (f ⊗ₘ g) := by
  let F := integerCoefficientExtension φ
  have h0 := congrArg (fun t => Functor.whiskerRight t F) (linearizedTensorIso_naturality f g)
  simp only [Functor.whiskerRight_comp] at h0
  have h1 := integerCoefficientSimplicialFreeIso_naturality φ (f ⊗ₘ g)
  have h : Functor.whiskerRight
      (simplicialIntegerTensorMap (linearizedSpaceMap f) (linearizedSpaceMap g)) F ≫
      (Functor.isoWhiskerRight (linearizedTensorIso X' Y') F ≪≫
        integerCoefficientSimplicialFreeIso φ (X' ⊗ Y')).hom =
    (Functor.isoWhiskerRight (linearizedTensorIso X Y) F ≪≫
        integerCoefficientSimplicialFreeIso φ (X ⊗ Y)).hom ≫
      Functor.whiskerRight (f ⊗ₘ g) (ModuleCat.free A) := by
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Category.assoc]
    rw [reassoc_of% h0, h1]
  let T := normalizedMooreComplex (ModuleCat A) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)
  have hh := congrArg T.map h
  simp only [Functor.map_comp] at hh
  exact hh

/-- 二因子の自由化比較のテンソルも指定鎖写像に自然。 -/
@[reassoc]
theorem integerCoefficientFreeTensorIso_naturality
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
        (linearizedSpaceMap f) (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat ⊗ₘ
      extendMap ((normalizedMooreComplex _).map (Functor.whiskerRight
        (linearizedSpaceMap g) (integerCoefficientExtension φ))) ComplexShape.embeddingDownNat) ≫
      (tensorIso (integerCoefficientFreeChainsIso φ X') (integerCoefficientFreeChainsIso φ Y')).hom =
    (tensorIso (integerCoefficientFreeChainsIso φ X) (integerCoefficientFreeChainsIso φ Y)).hom ≫
      (freeNegativeChainsMap (A := A) f ⊗ₘ freeNegativeChainsMap (A := A) g) := by
  change (_ ⊗ₘ _) ≫ (_ ⊗ₘ _) = (_ ⊗ₘ _) ≫ (_ ⊗ₘ _)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  exact congrArg₂ (fun a b => a ⊗ₘ b)
    (integerCoefficientFreeChainsIso_naturality φ f)
    (integerCoefficientFreeChainsIso_naturality φ g)

/-- 元の自由積鎖の指定 AW は両入力の全単体的射に自然。 -/
@[reassoc]
theorem freeProductAlexanderWhitney_naturality
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    freeNegativeChainsMap (A := A) (f ⊗ₘ g) ≫ freeProductAlexanderWhitney φ X' Y' =
      freeProductAlexanderWhitney φ X Y ≫
        (freeNegativeChainsMap (A := A) f ⊗ₘ freeNegativeChainsMap (A := A) g) := by
  apply (cancel_epi (integerCoefficientProductChainsIso φ X Y).hom).mp
  dsimp only [freeProductAlexanderWhitney]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← integerCoefficientProductChainsIso_naturality_assoc φ f g]
  simp only [Iso.hom_inv_id_assoc]
  erw [reassoc_of% (negativeCoefficientAlexanderWhitney_naturality φ
    (linearizedSpaceMap f) (linearizedSpaceMap g))]
  erw [integerCoefficientFreeTensorIso_naturality φ f g]

/-- 元の自由積鎖の指定 shuffle も両入力の全単体的射に自然。 -/
@[reassoc]
theorem freeProductShuffle_naturality
    {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (freeNegativeChainsMap (A := A) f ⊗ₘ freeNegativeChainsMap (A := A) g) ≫
        freeProductShuffle φ X' Y' =
      freeProductShuffle φ X Y ≫ freeNegativeChainsMap (A := A) (f ⊗ₘ g) := by
  apply (cancel_epi (tensorIso (integerCoefficientFreeChainsIso φ X)
    (integerCoefficientFreeChainsIso φ Y)).hom).mp
  dsimp only [freeProductShuffle]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← integerCoefficientFreeTensorIso_naturality_assoc φ f g]
  simp only [Iso.hom_inv_id_assoc]
  erw [reassoc_of% (negativeCoefficientShuffle_naturality φ
    (linearizedSpaceMap f) (linearizedSpaceMap g))]
  rw [integerCoefficientProductChainsIso_naturality]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
