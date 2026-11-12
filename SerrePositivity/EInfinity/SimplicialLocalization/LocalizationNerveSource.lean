module

public import SerrePositivity.EInfinity.SimplicialLocalization.HammockInvertsEdges

/-!
# 元の通常圏から既存の局所化 nerve への関手

概要：元の Kan hammock 比較の左逆を通じて既存 localizationNerve へ送る。
方針：実際の左右の nerve 同値を合成し、その元の可逆二胞体を保持する。
規約：選択した逆の頂点作用を恒等とは仮定しない。元の頂点との比較を供給する。
使われ方：元の指定射を反転する CAlg_R への関手と ∞ 局所化の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def kanHammockLocalizationEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (kanHammockNerve C) (localizationNerve C) :=
  (kanFreeHammockAugmentationNerve_equivalence C).choose.symm.trans
    (kanFreeHammockComparisonNerve_equivalence C).choose

lemma kanHammockLocalizationEquivalence_hom :
    (kanHammockLocalizationEquivalence C).hom =
      (kanFreeHammockAugmentationNerve_equivalence C).choose.inv ≫
        kanFreeHammockComparisonNerve C := rfl

def kanHammockLocalizationComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (kanFreeHammockAugmentationNerve C ≫
      (kanHammockLocalizationEquivalence C).hom) (kanFreeHammockComparisonNerve C) := by
  have h := (kanFreeHammockAugmentationNerve_equivalence C).choose.homInvIso.postcomp
    (kanFreeHammockComparisonNerve C)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((kanFreeHammockAugmentationNerve C ≫
      (kanFreeHammockAugmentationNerve_equivalence C).choose.inv) ≫
        kanFreeHammockComparisonNerve C) (𝟙 _ ≫ kanFreeHammockComparisonNerve C) at h
  simpa only [kanHammockLocalizationEquivalence_hom, Category.assoc, Category.id_comp] using h

def localizationNerveSourceMap : nerve C.category ⟶ localizationNerve C :=
  hammockLocalizationNerveMap C ≫ (kanHammockLocalizationEquivalence C).hom

lemma localizationNerveSourceMap_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (localizationNerveSourceMap C) (weakNerveEdges C) :=
  (hammockLocalizationNerveMap_inverts C).comp (kanHammockLocalizationEquivalence C).hom

def kanHammockLocalization_vertexIso (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((kanHammockLocalizationEquivalence C).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show KanHammockCategory C from X)))
      (localizationNerveVertexEquiv C (show KanLocalizationCategory C from X)) := by
  have h := (kanHammockLocalizationComparison C).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show KanFreeHammockCategory C from X))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((kanHammockLocalizationEquivalence C).hom.app _
      ((kanFreeHammockAugmentationNerve C).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show KanFreeHammockCategory C from X))))
    ((kanFreeHammockComparisonNerve C).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show KanFreeHammockCategory C from X))) at h
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (kanFreeHammockAugmentationFunctor C)
    (show KanFreeHammockCategory C from X)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex (kanFreeHammockComparisonFunctor C)
    (show KanFreeHammockCategory C from X)
  change (kanFreeHammockAugmentationNerve C).app _ _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show KanHammockCategory C from X) at hl
  change (kanFreeHammockComparisonNerve C).app _ _ =
    localizationNerveVertexEquiv C (show KanLocalizationCategory C from X) at hr
  rw [hl, hr] at h
  exact h

def localizationNerveSourceMap_vertexIso (X : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((localizationNerveSourceMap C).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X))
      (localizationNerveVertexEquiv C (show KanLocalizationCategory C from X)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((kanHammockLocalizationEquivalence C).hom.app _
      ((hammockLocalizationNerveMap C).app _ (ComposableArrows.mk₀ X))) _
  rw [hammockLocalizationNerveMap_vertex]
  exact kanHammockLocalization_vertexIso C X

end SerrePositivity.EInfinity.SimplicialLocalization
