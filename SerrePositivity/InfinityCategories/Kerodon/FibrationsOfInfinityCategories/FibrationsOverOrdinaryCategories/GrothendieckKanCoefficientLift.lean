module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveOver
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityMonoidal
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：元のGrothendieck射列の比較を、元の置換単位を固定してKan係数へ延長する。
方針：係数のEx∞単位によるweighted mapと、既存の相対left-anodyne延長を使う。
規約：延長の存在と二つの厳密な等式だけを主張する。前合成同値性は別の検収。
使われ方：IS-W2 R03dの指定された元の射を保つ比較の組み立て。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元の全Cat図式のnerveを、同じEx∞でKan係数にする。 -/
abbrev grothendieckKanCoefficients : I ⥤ SSet.{u} := (F ⋙ nerveFunctor) ⋙ exInfinity

local instance grothendieckKanCoefficients_kanComplex (i : I) :
    KanComplex ((grothendieckKanCoefficients F).obj i) := by
  change KanComplex (exInfinity.obj (nerve (F.obj i)))
  infer_instance

/-- 元の全係数の、同じEx∞単位による自然変換。 -/
def grothendieckKanCoefficientUnit : F ⋙ nerveFunctor ⟶ grothendieckKanCoefficients F :=
  Functor.whiskerLeft (F ⋙ nerveFunctor) exInfinityUnit

/-- 元のGrothendieck射列を、同じ底のKan係数のweighted nerveへ送る。 -/
def grothendieckKanCoefficientMap :
    nerve (Grothendieck F) ⟶ weightedNerve (grothendieckKanCoefficients F) :=
  grothWeightedNerveForward F ≫ weightedNerveMap (grothendieckKanCoefficientUnit F)

/-- 元の全係数の比較は、同じ底への射影を厳密に保つ。 -/
theorem grothendieckKanCoefficientMap_projection :
    grothendieckKanCoefficientMap F ≫ weightedNerveProjection (grothendieckKanCoefficients F) =
      nerveMap (Grothendieck.forget F) := by
  rw [grothendieckKanCoefficientMap, Category.assoc, weightedNerveMap_projection,
    grothWeightedNerveForward_projection]

/-- 元の単位を固定して相対延長する。延長の同値性はこの存在から主張しない。 -/
theorem exists_grothendieckKanCoefficientLift :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F := by
  dsimp only
  apply exists_relativeFunctorExtension_of_leftAnodyne
    (weightedNerveProjection (grothendieckKanCoefficients F))
    ((continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F)))).hom
    ((continuousLeftFibrationReplacementUnit (nerve I)).app _).left
    (continuousLeftFibrationReplacementUnit_leftAnodyne _)
    (grothendieckKanCoefficientMap F)
  rw [grothendieckKanCoefficientMap_projection]
  exact ((continuousLeftFibrationReplacementUnit (nerve I)).app
    (Over.mk (nerveMap (Grothendieck.forget F)))).w.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
