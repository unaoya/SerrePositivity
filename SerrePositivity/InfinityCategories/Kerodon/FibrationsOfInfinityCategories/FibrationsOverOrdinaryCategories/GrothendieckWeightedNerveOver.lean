module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationFilling

/-!
概要：同じweighted nerve比較を底上の同型とし、指定されたleft fibration置換へ送る。
方針：射影の厳密な等式をOver.isoMkに渡し、既存の置換関手と単位の自然性を使う。
規約：元の置換と単位を保持する。元の係数とのKan分類を主張しない。
使われ方：IS-W2 R03dの同じ底上の比較の組み立て。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 同じ射影を保つ厳密な比較は、同じ底のOverの同型である。 -/
def grothendieckWeightedNerveOverIso :
    Over.mk (nerveMap (Grothendieck.forget F)) ≅ Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)) :=
  Over.isoMk (grothendieckWeightedNerveIso F) (grothendieckWeightedNerveIso_projection F)

/-- 指定された同じleft fibration置換は、元の底上の比較同型を保つ。 -/
def grothendieckWeightedNerveReplacementIso :
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (nerveMap (Grothendieck.forget F))) ≅
    (continuousLeftFibrationReplacement (nerve I)).obj
      (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor))) :=
  (continuousLeftFibrationReplacement (nerve I)).mapIso (grothendieckWeightedNerveOverIso F)

/-- 同じ置換同型は、元の置換の単位と厳密に可換する。 -/
theorem grothendieckWeightedNerveReplacementIso_unit :
    ((continuousLeftFibrationReplacementUnit (nerve I)).app
      (Over.mk (nerveMap (Grothendieck.forget F)))).left ≫
        (grothendieckWeightedNerveReplacementIso F).hom.left =
      (grothendieckWeightedNerveOverIso F).hom.left ≫
        ((continuousLeftFibrationReplacementUnit (nerve I)).app
          (Over.mk (weightedNerveProjection (F ⋙ nerveFunctor)))).left :=
  congrArg (fun f => f.left)
    ((continuousLeftFibrationReplacementUnit (nerve I)).naturality
      (grothendieckWeightedNerveOverIso F).hom).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
