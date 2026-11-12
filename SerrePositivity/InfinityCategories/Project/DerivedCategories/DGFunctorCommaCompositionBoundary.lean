module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaCompositionMaps
/-!
概要：全 Hom tensor 上の合成比較差は、二つの同じ実比較差の合成の和になる。
方針：中央の実 augmentation の前後合成を移し、全パラメータで中間項を消す。
規約：高次の入力を捨てない。使われ方：comma dg 合成の実比較 cochain の微分式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 第一比較 cochain の後に合成する、同じ全 Hom の実鎖写像。 -/
def dgFunctorCommaFirstCompositionMap :
    homObject R E X.replacement (F.obj Y.source) ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z ⟶
        homObject R E X.replacement (F.obj Z.source) :=
  (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z) ≫
    eComp (Complex R) X.replacement (F.obj Y.source) (F.obj Z.source)
/-- 第二比較 cochain の後に合成する、同じ全 Hom の実鎖写像。 -/
def dgFunctorCommaSecondCompositionMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
      homObject R E Y.replacement (F.obj Z.source) ⟶
        homObject R E X.replacement (F.obj Z.source) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y ⊗ₘ 𝟙 _) ≫
    eComp (Complex R) X.replacement Y.replacement (F.obj Z.source)
/-- 第一比較差の tensor と実後合成を、同じ全 Hom 二因子の合成に戻す。 -/
lemma dgFunctorCommaFirstCompositionMap_boundary :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) ≫
        dgFunctorCommaFirstCompositionMap R C E F X Y Z =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z) ≫
          eComp (Complex R) X.replacement (F.obj Y.source) (F.obj Z.source) := by
  rw [dgFunctorCommaFirstCompositionMap, ← Category.assoc,
    whiskerRight_comp_tensorHom, Category.comp_id]
/-- 第二比較差についても、同じ全 Hom 二因子の合成に戻る。 -/
lemma dgFunctorCommaSecondCompositionMap_boundary :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ◁
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F Y Z) ≫
        dgFunctorCommaSecondCompositionMap R C E F X Y Z =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F Y Z) ≫
          eComp (Complex R) X.replacement Y.replacement (F.obj Z.source) := by
  rw [dgFunctorCommaSecondCompositionMap, ← Category.assoc,
    whiskerLeft_comp_tensorHom, Category.comp_id]
/-- 同じ実合成の比較差は、二つの実比較差の合成の和で与えられる。 -/
lemma dgFunctorCommaCompositeBoundary_decomposition :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) ≫
        dgFunctorCommaFirstCompositionMap R C E F X Y Z +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F Y Z) ≫
          dgFunctorCommaSecondCompositionMap R C E F X Y Z =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositeBoundary R C E F X Y Z := by
  rw [dgFunctorCommaFirstCompositionMap_boundary,
    dgFunctorCommaSecondCompositionMap_boundary,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositeBoundary_eq]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_boundary (V := Complex R) (ForgetEnrichment (Complex R) E)
    X.augmentation Y.augmentation Z.augmentation
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite]
    using! he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
