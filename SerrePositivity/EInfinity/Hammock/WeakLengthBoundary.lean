module

public import SerrePositivity.EInfinity.Hammock.LengthBoundaryFiniteUnion
public import SerrePositivity.EInfinity.Hammock.LengthBoundaryNaturality
public import SerrePositivity.EInfinity.Hammock.WeakFiniteUnion

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
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory
open SerrePositivity.InfinityCategories

variable {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

lemma lengthBoundaryMapsTo (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    ∀ k, Set.MapsTo ((η.app c).app k)
      ((lengthBoundary F n c).obj k) ((lengthBoundary G n c).obj k) := by
  intro k x hx
  obtain ⟨p⟩ := (lengthBoundary_mem_iff F n c k x).1 hx
  exact (lengthBoundary_mem_iff G n c k _).2 ⟨BoundaryPresentation.map η p⟩

lemma weakLengthBoundaryMap (hF : ProperDiagram F) (hG : ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (lengthBoundaryMap η n c) := by
  have hw := weakFiniteUnion (η.app c) (boundarySubsets n c)
    (subsetImage F c) (subsetImage G c) (subsetImage_inf F c hF)
    (subsetImage_inf G c hG) (subsetImageMapsTo c η) (weakSubsetImageMap c η hF hG hη)
  have hb := weakMapSubcomplex_of_eq (η.app c)
    (lengthBoundary_eq_finsetSup F n c).symm (lengthBoundary_eq_finsetSup G n c).symm
    _ (lengthBoundaryMapsTo η n c) hw
  have he : mapSubcomplex (η.app c) (lengthBoundaryMapsTo η n c) =
      lengthBoundaryMap η n c := by
    apply (cancel_mono (lengthBoundary G n c).ι).1
    rw [mapSubcomplex_ι, lengthBoundaryMap_ι]
  rwa [he] at hb

end SerrePositivity.EInfinity.Hammock
