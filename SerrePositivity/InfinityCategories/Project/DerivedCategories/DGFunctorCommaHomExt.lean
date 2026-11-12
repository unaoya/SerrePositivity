module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionHomExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHom
/-!
概要：分解 Hom 複体への射を、実入力・実出力・比較ホモトピーから厳密に回収する。
方針：mapping cocone の実二射影と次数ごとの恒等分解を使う。
規約：全パラメータ複体からの射を扱う。使われ方：comma dg 圏の合成則の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (K : Complex R)
/-- 同じ分解 Hom 複体への実射から、指定比較ホモトピーを回収する。 -/
def dgFunctorCommaHomComparison
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y) :
    Cochain K (homObject R E X.replacement (F.obj Y.source)) (-1) :=
  (Cochain.ofHom f).comp
    (mappingCocone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)) (zero_add _)
/-- 実二射影と比較ホモトピーが等しければ、全パラメータからの実射も等しい。 -/
lemma dgFunctorCommaHom_ext
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
    (ha : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y)
    (hb : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
    (ht : dgFunctorCommaHomComparison R C E F X Y K f =
      dgFunctorCommaHomComparison R C E F X Y K g) : f = g := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y
  have hp : f ≫ mappingCocone.fst d = g ≫ mappingCocone.fst d := by
    apply biprod.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap, Category.assoc] using ha
    · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap, Category.assoc] using hb
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext d f g hp ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories
