module

public import SerrePositivity.KST.NonConnective.DGKappaFullPerfAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge

/-!
概要：同じ dg 関手 Hom end 内の実閉射を、元の Perf の実自然変換へ送る。
方針：全 native 入力の辺を持ち上げ、全 Perf 作用に写して両端を厳密に照合する。
規約：閉射の可逆性は要求しない。使われ方：分裂 cofiber 族の実注入・射影。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  {F G : DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)}
  (f : ForgetEnrichment.of (Complex R) F ⟶ ForgetEnrichment.of (Complex R) G)

/-- 元の同じ閉射を、全 native 関手族の実辺として保持する。 -/
def dgKappaFullPerfClosedInputEdge : (dgKappaFullPerfParameter R D I).Edge
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex G)) :=
  SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, u + 1}
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) f))

/-- 全 Perf 作用に写した同じ閉射の辺。両端は元の厳密 Perf 作用そのもの。 -/
def dgKappaPerfClosedEdge :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) G))) :=
  ((dgKappaFullPerfClosedInputEdge R D I f).map (dgKappaFullPerfFamilyMap R D I)).ofEq
    (dgKappaFullPerfFamilyMap_vertex R D I F) (dgKappaFullPerfFamilyMap_vertex R D I G)

/-- 同じ閉射を、元の実 Perf 関手の全単体を保つ自然変換として読む。 -/
def dgKappaPerfClosedHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (dgKappaPerfClosedEdge R D I f).toTruncated

end SerrePositivity.KST.NonConnective
