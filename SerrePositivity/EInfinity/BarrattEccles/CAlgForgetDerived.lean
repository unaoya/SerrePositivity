module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgDerivedForgetSource
public import SerrePositivity.EInfinity.BarrattEccles.CAlgLocalizationUniversal
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LocalizationExtension

/-!
# 既存 CAlg_R から既存 D(R) への忘却 ∞ 関手

概要：元の通常忘却の D(R) 値解像を、完成した ∞ 局所化の普遍性で延長する。
方針：全反転関手 ∞ 圏の前合成同値から一つの実関手と全比較同型を選ぶ。
規約：既存 CAlg_R・既存 derivedInfinityCategory・元の通常忘却を保持する。
使われ方：離散入力・∞ 極限保存・G1′ の実忘却界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory SSet SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma cAlgForgetDerived_exists :
    ∃ U : CAlg_R A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource A ≫ U)
        (cofibrantAlgebraUnderlyingDerivedSource A)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.localization_extension_exists (cAlgLocalizationSource A)
    (weakNerveEdges (cofibrantAlgebraRelativeCategory A)) (cAlgLocalizationSource_inverts A)
    (cAlgLocalizationPrecomposition_isQCatEquivalence A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A))
    (cofibrantAlgebraUnderlyingDerivedSource A) (cofibrantAlgebraUnderlyingDerivedSource_inverts A)

def cAlgForgetDerived : CAlg_R A ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A :=
  Classical.choose (cAlgForgetDerived_exists A)

def cAlgForgetDerived_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cAlgLocalizationSource A ≫ cAlgForgetDerived A)
      (cofibrantAlgebraUnderlyingDerivedSource A) :=
  (Classical.choose_spec (cAlgForgetDerived_exists A)).some

def cAlgForgetDerived_sourceVertexIso (X : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)))
      ((cofibrantAlgebraUnderlyingDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (cAlgForgetDerived_sourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)

end SerrePositivity.EInfinity.BarrattEccles
