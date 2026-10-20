module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionCompositionPrimitives
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionHomExt
/-!
概要：出力分解の実 Hom 複体の間に、全次数を保持する実合成鎖写像を構成する。
方針：二つの実比較 cochain の和と、その全微分式で実二合成を cocone へ持ち上げる。
規約：単位・結合律は別途検証。使われ方：分解 dg 圏の eComp。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 同じ全 Hom tensor 上の、実合成を比較する一つの全 cochain。 -/
def dgModuleFunctorResolutionCompositePrimitive :=
  dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z +
    dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z
/-- 同じ実比較 cochain の微分は、合成入力と合成出力の同じ差の負。 -/
lemma dgModuleFunctorResolutionCompositePrimitive_boundary :
    δ (-1) 0 (dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom (dgModuleFunctorResolutionCompositeBoundary R C E F X Y Z) = 0 := by
  rw [← dgModuleFunctorResolutionCompositeBoundary_decomposition]
  exact complexComparison_add_boundary _ _ _ _
    (dgModuleFunctorResolutionFirstCompositePrimitive_boundary R C E F X Y Z)
    (dgModuleFunctorResolutionSecondCompositePrimitive_boundary R C E F X Y Z)
/-- 全実 Hom tensor から同じ分解 Hom への、実合成鎖写像。 -/
def dgModuleFunctorResolutionComposition :
    dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      dgModuleFunctorResolutionHomComplex R C E F Y Z ⟶
        dgModuleFunctorResolutionHomComplex R C E F X Z :=
  dgModuleFunctorResolutionHomLift R C E F X Z _
    (dgModuleFunctorResolutionSourceComposite R C E F X Y Z)
    (dgModuleFunctorResolutionReplacementComposite R C E F X Y Z)
    (dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z)
    (dgModuleFunctorResolutionCompositePrimitive_boundary R C E F X Y Z)
/-- 実合成の入力射影は、同じ実入力二射の豊穣合成。 -/
lemma dgModuleFunctorResolutionComposition_source :
    dgModuleFunctorResolutionComposition R C E F X Y Z ≫
      dgModuleFunctorResolutionSourceHomMap R C E F X Z =
        dgModuleFunctorResolutionSourceComposite R C E F X Y Z :=
  dgModuleFunctorResolutionHomLift_source R C E F X Z _ _ _ _ _
/-- 実合成の半自由出力射影は、同じ実出力二射の豊穣合成。 -/
lemma dgModuleFunctorResolutionComposition_replacement :
    dgModuleFunctorResolutionComposition R C E F X Y Z ≫
      dgModuleFunctorResolutionReplacementHomMap R C E F X Z =
        dgModuleFunctorResolutionReplacementComposite R C E F X Y Z :=
  dgModuleFunctorResolutionHomLift_replacement R C E F X Z _ _ _ _ _
/-- 実合成の比較 cochain は、構成した同じ二 cochain の和を厳密に回収する。 -/
lemma dgModuleFunctorResolutionComposition_comparison :
    dgModuleFunctorResolutionHomComparison R C E F X Z _
      (dgModuleFunctorResolutionComposition R C E F X Y Z) =
        dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgModuleFunctorResolutionHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (dgModuleFunctorResolutionDifference R C E F X Z)
    (biprod.lift (dgModuleFunctorResolutionSourceComposite R C E F X Y Z)
      (dgModuleFunctorResolutionReplacementComposite R C E F X Y Z))
    (dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z)
    (dgModuleFunctorResolutionCompositePrimitive_boundary R C E F X Y Z) p q hpq
end SerrePositivity.InfinityCategories
