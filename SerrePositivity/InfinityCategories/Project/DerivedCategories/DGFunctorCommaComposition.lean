module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaCompositionPrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt
/-!
概要：commaの実 Hom 複体の間に、全次数を保持する実合成鎖写像を構成する。
方針：二つの実比較 cochain の和と、その全微分式で実二合成を cocone へ持ち上げる。
規約：単位・結合律は別途検証。使われ方：comma dg 圏の eComp。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 同じ全 Hom tensor 上の、実合成を比較する一つの全 cochain。 -/
def dgFunctorCommaCompositePrimitive :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z +
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z
/-- 同じ実比較 cochain の微分は、合成入力と合成出力の同じ差の負。 -/
lemma dgFunctorCommaCompositePrimitive_boundary :
    δ (-1) 0 (dgFunctorCommaCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositeBoundary R C E F X Y Z) = 0 := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositeBoundary_decomposition]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexComparison_add_boundary _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive_boundary R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive_boundary R C E F X Y Z)
/-- 全実 Hom tensor から同じ分解 Hom への、実合成鎖写像。 -/
def dgFunctorCommaComposition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X Z _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite R C E F X Y Z)
    (dgFunctorCommaCompositePrimitive R C E F X Y Z)
    (dgFunctorCommaCompositePrimitive_boundary R C E F X Y Z)
/-- 実合成の入力射影は、同じ実入力二射の豊穣合成。 -/
lemma dgFunctorCommaComposition_source :
    dgFunctorCommaComposition R C E F X Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Z =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite R C E F X Y Z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R C E F X Z _ _ _ _ _
/-- 実合成の比較対象射影は、同じ実出力二射の豊穣合成。 -/
lemma dgFunctorCommaComposition_replacement :
    dgFunctorCommaComposition R C E F X Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Z =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite R C E F X Y Z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R C E F X Z _ _ _ _ _
/-- 実合成の比較 cochain は、構成した同じ二 cochain の和を厳密に回収する。 -/
lemma dgFunctorCommaComposition_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X Z _
      (dgFunctorCommaComposition R C E F X Y Z) =
        dgFunctorCommaCompositePrimitive R C E F X Y Z := by
  apply Cochain.ext
  intro p q hpq
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Z)
    (biprod.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite R C E F X Y Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite R C E F X Y Z))
    (dgFunctorCommaCompositePrimitive R C E F X Y Z)
    (dgFunctorCommaCompositePrimitive_boundary R C E F X Y Z) p q hpq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
