module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeEdges
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.F1.ColimitFullyFaithful
public import SerrePositivity.InfinityCategories.F1.ColimitHomotopyUniqueness
public import SerrePositivity.InfinityCategories.Core.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Core.RelativeInitialVertices

/-! # 普遍余錐間の比較の可逆性

概要：普遍余錐間のホモトピーは、基底図式への制限が可逆なら全体も可逆である。
方針：普遍余錐の全部分圏に辺を持ち上げ、図式への充満忠実射影で可逆性を反映する。
規約：全ての図式での余極限の存在は要求しない。使われ方：cofiber の選択・図式の同型不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：基底への像が可逆な普遍余錐間のホモトピーは可逆である。
方針：普遍余錐全体の h の射に持ち上げ、射影の充満忠実性で同型を反映する。
規約：両端の余極限性だけを使う。使われ方：普遍余錐全体の同型判定。 -/
lemma colimitCoconeHomotopy_isInvertible_of_restriction {K X : SSet.{u}}
    [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (H : SSet.Homotopy c.val d.val)
    (hH : IsIso ((hoFunctor.map (coconeRestriction K X)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
  let i := (relativeInitialVertices (coconeRestriction K X)).ι
  let u := SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge c d hc hd H)
  let F := (hoFunctor.map (colimitCoconeProjection K X)).toFunctor
  have hu : (hoFunctor.map i).toFunctor.map u =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) :=
    congrArg SSet.Truncated.HomotopyCategory.homMk (colimitCoconeHomotopyEdge_map c d hc hd H)
  let : F.Full := (colimitCoconeProjectionHoFullyFaithful K X).full
  let : F.Faithful := (colimitCoconeProjectionHoFullyFaithful K X).faithful
  have hFu : IsIso (F.map u) := by
    change IsIso ((hoFunctor.map (coconeRestriction K X)).toFunctor.map
      ((hoFunctor.map i).toFunctor.map u))
    rw [hu]
    exact hH
  let := hFu
  have huIso : IsIso u := isIso_of_reflects_iso u F
  let := huIso
  have hi := (hoFunctor.map i).toFunctor.map_isIso u
  rw [hu] at hi
  exact hi

/-- 概要：基底へ制限したホモトピーが可逆なら普遍余錐全体のホモトピーも可逆である。
方針：制限と関手辺の前合成の一致を用いて前補題に帰着する。
規約：値域は quasicategory。使われ方：実際の図式の比較を入力する形。 -/
lemma colimitCoconeHomotopy_isInvertible_of_precomp {K X : SSet.{u}}
    [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (H : SSet.Homotopy c.val d.val)
    (hH : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (stableHomotopyPrecomp (joinInl K Δ[0]) H))) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
  apply colimitCoconeHomotopy_isInvertible_of_restriction c d hc hd H
  change IsIso ((hoFunctor.map ((pre (joinInl K Δ[0])).app X)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
  rw [homMk_functorEdge_precomp]
  exact hH

end SerrePositivity.InfinityCategories
