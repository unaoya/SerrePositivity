module

public import SerrePositivity.KST.LocalizingInvariants.CofiberBottomLifting
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationComparisonProjection

/-!
概要：同じ底辺を持つ cofiber 図式の全族を、底辺で恒等となる同型で比較する。
方針：底辺評価の自明 Kan fiber 内の比較を使い、その射影の恒等式を保持する。
規約：cofiber 頂点だけの比較ではない。使われ方：商での元の cofiber の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {A : SSet.{u}}
  (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.space X) (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X)

def relativeComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X) f g h

lemma relativeComparison_bottom_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (relativeComparison X f g h) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X)).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X)) :
        hoFunctor.obj ((ihom A).obj ((ihom (Δ[1] : SSet.{u})).obj X)))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIsoOfTrivialKanFibration_projection_arrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom X) f g h

def relativeSquareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion X) (g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (relativeComparison X f g h) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.inclusion X)

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
