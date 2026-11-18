module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordSubsetImages
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakRange

/-!
# proper 図式の元の列部分集合の像の比較

概要：列部分集合の像は交わりを保ち、成分ごとの弱同値は同じ元の像の比較を弱同値にする。
方針：元の部分語の包含の像と proper の二条件を使う。
規約：比較は元の自然変換の制限。像の語を別のモデルへ置き換えない。
使われ方：元の境界の有限和の弱同値性。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)

def subsetImage (s : Finset (Fin c.length)) : (F.obj c).Subcomplex :=
  Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s))

lemma subsetImage_inf (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (s t : Finset (Fin c.length)) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c (s ⊓ t) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c s ⊓ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c t := by
  have he := hF.intersection_range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective c s) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective c t)
  calc
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c (s ⊓ t) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s) ∩
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c t)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage_subwordInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage_subwordInclusion]
      rfl
    _ = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c s ⊓ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c t := he

lemma range_eq_subsetImage {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (hf : Function.Injective f.orderHom) :
    Subfunctor.range (F.map f) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f) := by
  obtain ⟨h, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_image_eq f hf
  calc
    Subfunctor.range (F.map f) = Subfunctor.range (F.map (eqToHom h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion f)) :=
      congrArg (fun g : a ⟶ c => Subfunctor.range (F.map g)) he.symm
    _ = Subfunctor.range (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion f)) := by
      rw [CategoryTheory.Functor.map_comp, Subfunctor.range_comp,
        Subfunctor.range_eq_top, Subfunctor.image_top]
    _ = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f) := rfl

variable {F} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}} (η : F ⟶ G)

lemma subsetImageMapsTo (s : Finset (Fin c.length)) :
    ∀ k, Set.MapsTo ((η.app c).app k) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage F c s).obj k) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImage G c s).obj k) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mapsToRange (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s)) (G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s))
    (η.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword c s)) (η.app c) (η.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s))

lemma weakSubsetImageMap (hF : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram F) (hG : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram G)
    (hη : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app a)) (s : Finset (Fin c.length)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.mapSubcomplex (η.app c) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.subsetImageMapsTo c η s)) := by
  have := hF.map_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective c s)
  have := hG.map_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective c s)
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakRangeMap (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s)) (G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s))
    (η.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword c s)) (η.app c) (η.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s))
    (hη (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword c s))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
