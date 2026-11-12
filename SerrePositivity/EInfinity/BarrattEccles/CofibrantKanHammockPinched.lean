module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusion
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameRightKan
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinched
public import SerrePositivity.EInfinity.Hammock.ExInfinityWeakMap

/-!
# 元の全代数 hammock から cofibrant の同じ pinched Hom への弱比較

概要：元の cofibrant 包含を同じ Ex∞ で送り、その実逆を同じ Hom 比較へ接続する。
方針：既証の包含の弱同値性と Kan Whitehead から逆データを一度選ぶ。
規約：元の包含・元の二つの Hom・同じ q の端点を保持する。
使われ方：元の積単体の基準射を実 ProductHomMap の標的へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SimplicialLocalization Hammock
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantKanHammockInclusionMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (algebraReducedHammock A X.obj Y.obj) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((reducedColimitIso (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (show (cofibrantAlgebraRelativeCategory A).category from X)
    (show (cofibrantAlgebraRelativeCategory A).category from Y)).hom ≫
      cofibrantAlgebraHammockInclusionMap A _ _)

lemma cofibrantKanHammockInclusionMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantKanHammockInclusionMap A X Y) :=
  exInfinity_map_weak _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (reducedColimitIso (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y))).isWeakHomotopyEquivalence.comp
        (cofibrantAlgebraHammockInclusionMap_weak A _ _))

def cofibrantKanHammockInclusionEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (algebraReducedHammock A X.obj Y.obj)) :=
  by
    have h := (cofibrantKanHammockInclusionMap_weak A X Y).isSimplicialHomotopyEquivalence
    exact h.isQCatEquivalence.choose

lemma cofibrantKanHammockInclusionEquivalence_hom :
    (cofibrantKanHammockInclusionEquivalence A X Y).hom =
      cofibrantKanHammockInclusionMap A X Y := rfl

def cofibrantHammockPinchedReferenceMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (algebraReducedHammock A X.obj Y.obj) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (cofibrantHammockVertex A X) (cofibrantHammockVertex A Y) :=
  (cofibrantKanHammockInclusionEquivalence A X Y).inv ≫
    kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)

lemma cofibrantHammockPinchedReferenceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantHammockPinchedReferenceMap A X Y) := by
  have hi := (cofibrantKanHammockInclusionEquivalence A X Y).symm.isQCatEquivalence
  exact hi.isWeakHomotopyEquivalence.comp
    (kanHammockHomPinchedMap_weak (cofibrantAlgebraRelativeCategory A)
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y))

def cofibrantHammockPinchedReferenceMap_inclusion : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (cofibrantKanHammockInclusionMap A X Y ≫ cofibrantHammockPinchedReferenceMap A X Y)
    (kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)) := by
  simpa only [cofibrantHammockPinchedReferenceMap,
    ← cofibrantKanHammockInclusionEquivalence_hom, Category.assoc, Category.id_comp] using
      (cofibrantKanHammockInclusionEquivalence A X Y).homInvIso.postcomp
        (kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
          (show (cofibrantAlgebraRelativeCategory A).category from X)
          (show (cofibrantAlgebraRelativeCategory A).category from Y))

end SerrePositivity.EInfinity.BarrattEccles
