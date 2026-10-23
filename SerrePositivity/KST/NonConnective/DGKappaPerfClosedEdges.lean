module

public import SerrePositivity.KST.NonConnective.DGKappaFullPerfAction
public import SerrePositivity.InfinityCategories.F1.UniverseInvertibleEdge

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
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  {F G : DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)}
  (f : ForgetEnrichment.of (Complex R) F ⟶ ForgetEnrichment.of (Complex R) G)

/-- 元の同じ閉射を、全 native 関手族の実辺として保持する。 -/
def dgKappaFullPerfClosedInputEdge : (dgKappaFullPerfParameter R D I).Edge
    (ULift.up (Simplex.vertex F)) (ULift.up (Simplex.vertex G)) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge.{max (u + 1) v, u + 1}
    (X := dgNerve R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)))
    (dgClosedEdge R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) f))

/-- 全 Perf 作用に写した同じ閉射の辺。両端は元の厳密 Perf 作用そのもの。 -/
def dgKappaPerfClosedEdge :
    ((ihom (dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).obj
      (dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))).Edge
      (functorVertex (dgNerve.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F)))
      (functorVertex (dgNerve.map
        (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) G))) :=
  ((dgKappaFullPerfClosedInputEdge R D I f).map (dgKappaFullPerfFamilyMap R D I)).ofEq
    (dgKappaFullPerfFamilyMap_vertex R D I F) (dgKappaFullPerfFamilyMap_vertex R D I G)

/-- 同じ閉射を、元の実 Perf 関手の全単体を保つ自然変換として読む。 -/
def dgKappaPerfClosedHomotopy : SSet.Homotopy
    (dgNerve.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) F))
    (dgNerve.map (presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I) G)) :=
  simplicialHomotopyOfFunctorEdge (dgKappaPerfClosedEdge R D I f).toTruncated

end SerrePositivity.KST.NonConnective
