module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaAssociativityMaps
/-!
概要：比較 cochain を後合成する実二作用の三つの結合式を証明する。
方針：実入力像・実比較対象の合成保存と、全パラメータ豊穣結合律を使う。
使われ方：comma dg 圏の結合律の三つの比較項。
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
/-- 実合成の入力像は、実入力像同士の豊穣合成。 -/
lemma dgFunctorCommaComposition_image
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Z =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z) ≫
        eComp (Complex R) (F.obj X.source) (F.obj Y.source) (F.obj Z.source) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceComposite_image]
variable (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 第一比較項を輸送する実作用の結合式。 -/
lemma dgFunctorCommaFirstCompositionMap_assoc :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F W X Y ▷
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F W Y Z =
    (α_ (homObject R E W.replacement (F.obj X.source))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
      (homObject R E W.replacement (F.obj X.source)) ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F W X Z := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    dgFunctorCommaComposition_image]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_associativity (Complex R) E
    W.replacement (F.obj X.source) (F.obj Y.source) (F.obj Z.source) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z)
/-- 中央比較項を輸送する、第一・第二実作用の混合結合式。 -/
lemma dgFunctorCommaMixedCompositionMap_assoc :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F W X Y ▷
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F W Y Z =
    (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
      (homObject R E X.replacement (F.obj Y.source))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F X Y Z ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F W X Z := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_associativity (Complex R) E
    W.replacement X.replacement (F.obj Y.source) (F.obj Z.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F W X) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F Y Z)
/-- 第三比較項を輸送する実作用の結合式。 -/
lemma dgFunctorCommaSecondCompositionMap_assoc :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F W X Y ▷
        (homObject R E Y.replacement (F.obj Z.source)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F W Y Z =
    (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E Y.replacement (F.obj Z.source))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F X Y Z ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F W X Z := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, Category.assoc,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_replacement,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementComposite]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterEnriched_associativity (Complex R) E
    W.replacement X.replacement Y.replacement (F.obj Z.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F W X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y) (𝟙 _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
