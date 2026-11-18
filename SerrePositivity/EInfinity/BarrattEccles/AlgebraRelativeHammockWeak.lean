module

public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeComparisons
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalenceWeak

/-!
# 元の包含・置換による hammock Hom 射自身の弱同値性

概要：元の同じ相対包含と置換の両方向の Hom 射を弱同値と証明する。
方針：元の両指定比較自然変換を相対逆の一般判定へ渡す。
規約：元の cofibrant 代数と元の全代数の Hom を保持する。
使われ方：実 DK Hom と元の Map^h の高次比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]
lemma cofibrantToAlgebraDK_colimitMap_weak
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap (cofibrantToAlgebraDKRelative A) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.colimitMap_weak (cofibrantToAlgebraDKRelative A)
    (algebraToCofibrantDKRelative A) (cofibrantDKComparison A) (cofibrantDKComparison_weak A)
    (algebraDKComparison A) (algebraDKComparison_weak A) X Y
lemma algebraToCofibrantDK_colimitMap_weak (X Y : (algebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap (algebraToCofibrantDKRelative A) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.colimitMap_weak (algebraToCofibrantDKRelative A)
    (cofibrantToAlgebraDKRelative A) (algebraDKComparison A) (algebraDKComparison_weak A)
    (cofibrantDKComparison A) (cofibrantDKComparison_weak A) X Y
lemma cofibrantToAlgebraDK_reducedMap_weak
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap (cofibrantToAlgebraDKRelative A) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.reducedMap_weak (cofibrantToAlgebraDKRelative A)
    (algebraToCofibrantDKRelative A) (cofibrantDKComparison A) (cofibrantDKComparison_weak A)
    (algebraDKComparison A) (algebraDKComparison_weak A) X Y
lemma algebraToCofibrantDK_reducedMap_weak (X Y : (algebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap (algebraToCofibrantDKRelative A) X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeEquivalence.reducedMap_weak (algebraToCofibrantDKRelative A)
    (cofibrantToAlgebraDKRelative A) (algebraDKComparison A) (algebraDKComparison_weak A)
    (cofibrantDKComparison A) (cofibrantDKComparison_weak A) X Y
end SerrePositivity.EInfinity.BarrattEccles
