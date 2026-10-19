module

public import SerrePositivity.InfinityCategories.F1B.KanPullbackCartesianPair
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomPostCartesian
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseRelativeTargetInner
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinCartesianRestriction

/-!
概要：相対 join の全空間の相対比較は底方向の cartesian 輸送を保つ。
方針：制限と後合成が保つ cartesian 辺を、引き戻しの両成分の判定で合わせる。
規約：標的の射の後合成の inner fibration 性を仮定し、境界制限では証明済みの性質を使う。
使われ方：局所相対余錐の普遍性を全空間へ移すための輸送の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対 join の相対比較は底への cartesian 辺を保存する。
方針：第一成分の制限と第二成分の後合成の保存性を引き戻しの判定へ渡す。
規約：標的の射 U の全空間での後合成は inner fibration。
使われ方：fiber の始点境界充填を全空間へ移す際の保存性の前提。 -/
lemma kanRelativeJoinRelativeRestriction_preservesCartesianEdges {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E)
    [InnerFibration (kanFiberwiseHomPostcomp p U)]
    (e : (kanFiberwiseHom (relativeJoinBaseProjection p (𝟙 C)) D) _⦋1⦌)
    (he : IsCartesianEdge
      (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D) e) :
    IsCartesianEdge (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U)
      ((kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U).app
        (Opposite.op ⦋1⦌) e) := by
  let i := kanRelativeJoinInlOver p
  let e' := (kanFiberwiseRelativeRestriction i U).app (Opposite.op ⦋1⦌) e
  have hfst : (pullback.fst (kanFiberwiseHomPostcomp p U)
      (kanFiberwiseHomPre (D := E) i)).app (Opposite.op ⦋1⦌) e' =
      (kanFiberwiseHomPre (D := D) i).app (Opposite.op ⦋1⦌) e :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (kanFiberwiseRelativeRestriction_fst i U) (Opposite.op ⦋1⦌)) e
  have hsnd : (pullback.snd (kanFiberwiseHomPostcomp p U)
      (kanFiberwiseHomPre (D := E) i)).app (Opposite.op ⦋1⦌) e' =
      (kanFiberwiseHomPostcomp (relativeJoinBaseProjection p (𝟙 C)) U).app
        (Opposite.op ⦋1⦌) e :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (kanFiberwiseRelativeRestriction_snd i U) (Opposite.op ⦋1⦌)) e
  apply kanIsCartesianEdge_pullback_over
    (kanFiberwiseHomProjection p D)
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) E)
    (kanFiberwiseHomProjection p E)
    (kanFiberwiseHomPostcomp p U) (kanFiberwiseHomPre (D := E) i)
    (kanFiberwiseHomPostcomp_projection p U) (kanFiberwiseHomPre_projection i) e'
  · rw [hfst]
    exact kanRelativeJoinRestriction_preservesCartesianEdges p e he
  · erw [hsnd]
    exact kanFiberwiseHomPostcomp_preservesCartesianEdges _ U e he
  · rw [hfst]
    exact kanFiberwiseHomPostcomp_preservesCartesianEdges p U _
      (kanRelativeJoinRestriction_preservesCartesianEdges p e he)

end SerrePositivity.InfinityCategories.F1B
