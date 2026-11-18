module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundaryFiniteUnion
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundaryNaturality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakFiniteUnion

/-!
# proper 図式の元の長さ境界の弱同値

概要：proper 図式間の成分ごとの弱同値は元の長さ境界の比較を弱同値にする。
方針：列部分集合の像の交わりと有限和表示に、有限和の貼り合わせを適用する。
規約：結論の射は元の自然変換が誘導する lengthBoundaryMap そのものである。
使われ方：長さ濾過の段階の弱同値の帰納。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

lemma lengthBoundaryMapsTo (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    ∀ k, Set.MapsTo ((η.app c).app k)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary F n c).obj k) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary G n c).obj k) := by
  intro k x hx
  obtain ⟨p⟩ := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_mem_iff F n c k x).1 hx
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_mem_iff G n c k _).2 ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.BoundaryPresentation.map η p⟩

lemma weakLengthBoundaryMap (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c) := by
  have hw := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakFiniteUnion (η.app c) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.boundarySubsets n c)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage G c) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage_inf F c hF)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage_inf G c hG) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImageMapsTo c η) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakSubsetImageMap c η hF hG hη)
  have hb := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakMapSubcomplex_of_eq (η.app c)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_eq_finsetSup F n c).symm (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_eq_finsetSup G n c).symm
    _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMapsTo η n c) hw
  have he : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mapSubcomplex (η.app c) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMapsTo η n c) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap η n c := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary G n c).ι).1
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mapSubcomplex_ι, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryMap_ι]
  rwa [he] at hb

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
