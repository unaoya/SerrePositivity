module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionCompositionMaps
/-!
概要：全 Hom tensor 上の合成比較差は、二つの同じ実比較差の合成の和になる。
方針：中央の実 augmentation の前後合成を移し、全パラメータで中間項を消す。
規約：高次の入力を捨てない。使われ方：分解 dg 合成の実比較 cochain の微分式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 第一比較 cochain の後に合成する、同じ全 Hom の実鎖写像。 -/
def dgModuleFunctorResolutionFirstCompositionMap :
    moduleHom R E X.replacement.val (F.obj Y.source) ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z ⟶
        moduleHom R E X.replacement.val (F.obj Z.source) :=
  (𝟙 _ ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F Y Z) ≫
    eComp (Complex R) X.replacement.val (F.obj Y.source) (F.obj Z.source)
/-- 第二比較 cochain の後に合成する、同じ全 Hom の実鎖写像。 -/
def dgModuleFunctorResolutionSecondCompositionMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      moduleHom R E Y.replacement.val (F.obj Z.source) ⟶
        moduleHom R E X.replacement.val (F.obj Z.source) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y ⊗ₘ 𝟙 _) ≫
    eComp (Complex R) X.replacement.val Y.replacement.val (F.obj Z.source)
/-- 第一比較差の tensor と実後合成を、同じ全 Hom 二因子の合成に戻す。 -/
lemma dgModuleFunctorResolutionFirstCompositionMap_boundary :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z) ≫
        dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F Y Z) ≫
          eComp (Complex R) X.replacement.val (F.obj Y.source) (F.obj Z.source) := by
  rw [dgModuleFunctorResolutionFirstCompositionMap, ← Category.assoc,
    whiskerRight_comp_tensorHom, Category.comp_id]
/-- 第二比較差についても、同じ全 Hom 二因子の合成に戻る。 -/
lemma dgModuleFunctorResolutionSecondCompositionMap_boundary :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ◁
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F Y Z) ≫
        dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F Y Z) ≫
          eComp (Complex R) X.replacement.val Y.replacement.val (F.obj Z.source) := by
  rw [dgModuleFunctorResolutionSecondCompositionMap, ← Category.assoc,
    whiskerLeft_comp_tensorHom, Category.comp_id]
/-- 同じ実合成の比較差は、二つの実比較差の合成の和で与えられる。 -/
lemma dgModuleFunctorResolutionCompositeBoundary_decomposition :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z) ≫
        dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z +
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F Y Z) ≫
          dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositeBoundary R C E F X Y Z := by
  rw [dgModuleFunctorResolutionFirstCompositionMap_boundary,
    dgModuleFunctorResolutionSecondCompositionMap_boundary,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositeBoundary_eq]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_boundary (V := Complex R) (ModuleCategory R E)
    X.augmentation Y.augmentation Z.augmentation
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementComposite]
    using! he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
