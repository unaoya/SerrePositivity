module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockSourceFunctor
public import SerrePositivity.EInfinity.Hammock.CoherentComponents
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WeakArrowRoundTripComposition

/-!
# 元の指定射の Kan hammock nerve 内での反転

概要：元の backward hammock を逆辺とし、既存の二つの往復ホモトピーを送る。
方針：同じ Ex∞ 単位への後合成と coherent Hom の連結成分比較を使う。
規約：元の W の射と実際の通常関手の像を保持する。
使われ方：元の通常圏からの ∞ 局所化関手の反転条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.EInfinity.Hammock _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category} (f : X ⟶ Y)
  (hf : C.weakEquivalences f)

def kanHammockBackward : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y ⟶
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X :=
  (exInfinityEnrichedUnit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C)).forget.map
    (ForgetEnrichment.homOf SSet.{u} (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C) (X := Y) (Y := X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap f hf))

lemma kanHammock_source_homotopy :
    Nonempty (SSet.Homotopy
      (eHomEquiv SSet (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X)))
      (eHomEquiv SSet ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockBackward C f hf))) := by
  let U := (exInfinityEnrichedUnit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C)).forget
  let a := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).map f
  let b := ForgetEnrichment.homOf SSet.{u} (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C) (X := Y) (Y := X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap f hf)
  have H : SSet.Homotopy
      (eHomEquiv SSet (U.map (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).obj X))))
      (eHomEquiv SSet (U.map (a ≫ b))) := by
    change SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit C.weakEquivalences X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X X))
      (((λ_ (𝟙_ SSet.{u})).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap f hf) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences X Y X) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X X))
    exact HomotopyClasses.postHomotopy _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceCompositeHomotopy f hf)
  have hi : U.map (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).obj X)) =
      𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) := U.map_id _
  have hc : U.map (a ≫ b) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockBackward C f hf := U.map_comp _ _
  rw [hi, hc] at H
  exact ⟨H⟩

lemma kanHammock_target_homotopy :
    Nonempty (SSet.Homotopy
      (eHomEquiv SSet (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockBackward C f hf ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f))
      (eHomEquiv SSet (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y)))) := by
  let U := (exInfinityEnrichedUnit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C)).forget
  let a := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).map f
  let b := ForgetEnrichment.homOf SSet.{u} (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C) (X := Y) (Y := X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap f hf)
  have H : SSet.Homotopy (eHomEquiv SSet (U.map (b ≫ a)))
      (eHomEquiv SSet (U.map (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).obj Y)))) := by
    change SSet.Homotopy
      (((λ_ (𝟙_ SSet.{u})).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitRowComposition.backwardMap f hf ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition C.weakEquivalences Y X Y) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit C.weakEquivalences Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences Y Y))
    exact HomotopyClasses.postHomotopy _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetCompositeHomotopy f hf)
  have hi : U.map (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).obj Y)) =
      𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y) := U.map_id _
  have hc : U.map (b ≫ a) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockBackward C f hf ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f := U.map_comp _ _
  rw [hi, hc] at H
  exact ⟨H⟩

include hf in
lemma kanHammockSourceFunctor_weak_invertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)) := by
  let a := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f
  let b := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockBackward C f hf
  obtain ⟨hu⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammock_source_homotopy C f hf
  obtain ⟨hc⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammock_target_homotopy C f hf
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).toTruncated, ?_, ?_⟩⟩
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ b)).toTruncated :=
        SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a b).toTruncated
      _ = SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X))).toTruncated :=
        (coherentEdge_homMk_eq_of_homotopy _ _ hu).symm
      _ = 𝟙 _ := by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]
  · calc
      _ = SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (b ≫ a)).toTruncated :=
        SSet.Truncated.HomotopyCategory.homMk_comp_homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct b a).toTruncated
      _ = SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj Y))).toTruncated :=
        coherentEdge_homMk_eq_of_homotopy _ _ hc
      _ = 𝟙 _ := by simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
        SSet.Truncated.HomotopyCategory.homMk_id]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
