module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBoundary
/-!
概要：同じcomma Hom の実比較 cochain を、入力・出力の二実作用の差へ接続する。
方針：mapping cocone の全微分式と、同じ実二射影の差の定義を展開する。
規約：全 Hom 複体をパラメータに保持。使われ方：comma dg 圏の実合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 元の dg 関手の、同じ実入力射影上の全 Hom 作用。 -/
def dgFunctorCommaImageHomMap :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      homObject R E (F.obj X.source) (F.obj Y.source) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y ≫ F.map X.source Y.source
/-- 全 Hom 複体をパラメータとする、実比較 cochain。 -/
def dgFunctorCommaPrimitive :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E X.replacement (F.obj Y.source)) (-1) :=
  mappingCocone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)
/-- 同じ二射影による、比較正方形の実差。 -/
def dgFunctorCommaBoundary :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      homObject R E X.replacement (F.obj Y.source) :=
  dgFunctorCommaImageHomMap R C E F X Y ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source)) -
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
        Y.augmentation
/-- 同じ実差は、mapping cocone の第一射影と元の差写像の合成。 -/
lemma dgFunctorCommaBoundary_eq :
    mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y =
        dgFunctorCommaBoundary R C E F X Y := by
  let p := mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)
  change p ≫ (biprod.fst ≫ F.map X.source Y.source ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj Y.source)) -
      biprod.snd ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation) =
    ((p ≫ biprod.fst) ≫ F.map X.source Y.source) ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj Y.source)) -
      (p ≫ biprod.snd) ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation
  simp only [Preadditive.comp_sub, Category.assoc]
  rfl
/-- 全 Hom 上の同じ実比較 cochain の微分は、同じ実差の負。 -/
lemma dgFunctorCommaPrimitive_boundary :
    δ (-1) 0 (dgFunctorCommaPrimitive R C E F X Y) +
      Cochain.ofHom (dgFunctorCommaBoundary R C E F X Y) = 0 := by
  rw [← dgFunctorCommaBoundary_eq]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
