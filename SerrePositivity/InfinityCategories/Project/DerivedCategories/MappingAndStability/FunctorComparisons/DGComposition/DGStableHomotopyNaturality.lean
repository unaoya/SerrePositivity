module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGNerveH0Naturality
/-!
概要：通常の h と H⁰ の比較同値を、同じ実 dg nerve 射に対して自然同型にする。
方針：二切断との自然性を比較同値の逆へ移送し、実 H⁰ 自然性と合成する。
規約：全射に自然な比較を使う。使われ方：実出力分解の主導来作用への照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ dg 関手について、通常の h から H⁰ への全関手の自然性。 -/
def dgStableHomotopyEquivalence_naturalityIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)).toFunctor ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R D).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor ⋙ F.onHomotopy := by
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
  let B' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
  let hF := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)).toFunctor
  let tF := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
  have e : tF ⋙ B'.functor ≅ B.functor ⋙ hF :=
    eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.bridge_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))
  have ei : B.inverse ⋙ tF ≅ hF ⋙ B'.inverse :=
    CategoryTheory.Iso.inverseCompIso (CategoryTheory.Iso.isoCompInverse e ≪≫
      Functor.associator B.functor hF B'.inverse)
  exact (Functor.associator hF B'.inverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R D)).symm ≪≫
    Functor.isoWhiskerRight ei.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R D) ≪≫
    Functor.associator B.inverse tF (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R D) ≪≫
    Functor.isoWhiskerLeft B.inverse (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveMap_toH0_naturality R C D F)) ≪≫
    (Functor.associator B.inverse (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R C) F.onHomotopy).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
