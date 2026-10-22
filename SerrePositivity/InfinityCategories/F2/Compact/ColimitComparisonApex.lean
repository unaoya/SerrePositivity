module

public import SerrePositivity.InfinityCategories.Stable.CoconeLeg
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.F1.IntervalCosliceSource

/-!
概要：元の指定余錐間の比較辺は、両像が余極限なら像の頂点で可逆。
方針：同じ余錐辺を coslice 後合成で写し、始対象間の可逆性を射影する。
規約：元の比較辺と元の後合成射を保持。使われ方：全 Hom 錐の底図式での比較反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の余錐辺を頂点へ射影した同じ辺。 -/
def colimitComparisonApexEdge {J X : SSet.{u}} {p : J ⟶ X} {c d : JoinCocone p}
    (e : (sliceUnder p).Edge c d) : X.Edge c.vertex d.vertex :=
  e.map (sliceUnderProjection p)

/-- 元の両余錐像が余極限なら、元の同じ比較辺の頂点像は可逆。 -/
lemma colimitComparisonApex_map_isInvertible {J X Y : SSet.{u}} [Quasicategory Y]
    {p : J ⟶ X} (q : X ⟶ Y) {c d : JoinCocone p}
    (hc : IsColimitCone (mapJoinCocone q c)) (hd : IsColimitCone (mapJoinCocone q d))
    (e : (sliceUnder p).Edge c d) :
    IsInvertibleEdge ((colimitComparisonApexEdge e).map q) := by
  let e' := e.map (sliceUnderPostcomp p q)
  have hi : IsInvertibleEdge e' := isIso_of_isInitial hc.isInitialHo hd.isInitialHo _
  have h := hi.map (sliceUnderProjection (p ≫ q))
  have he : (e'.map (sliceUnderProjection (p ≫ q))).edge =
      ((colimitComparisonApexEdge e).map q).edge := by
    exact congrArg (fun f : sliceUnder p ⟶ Y => f.app (Opposite.op ⦋1⦌) e.edge)
      (sliceUnderPostcomp_projection p q)
  exact (isInvertibleEdge_congr he).mp h

end SerrePositivity.InfinityCategories.F2.Compact
