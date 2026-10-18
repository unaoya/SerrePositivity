module

public import SerrePositivity.InfinityCategories.F1.StrictDiagramMappingEvaluation
public import SerrePositivity.InfinityCategories.F1.LeftScaffoldComparison
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverEquivalence

/-!
概要：strict transport の写像空間上の作用に対する片側の逆。
方針：strict な変換を universal scaffold で評価し、scaffold に沿う相対前合成の同値を戻す。
規約：反対側の合成の恒等との比較と、coherent な変換空間との同値は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6、一般の nerve 上の写像空間の同値の逆データの構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：universal scaffold による前合成は left fibration への相対 Hom の同値を与える。
方針：scaffold の前合成同値性を底上の射に関する相対 Hom の同値へ移す。
規約：p が scaffold の始域を決め、q が相対 Hom の標的を決める。
使われ方：Kerodon Construction 5.3.4.7、Corollary 5.6.0.6、strict な変換の評価を元の相対 Hom へ戻す。 -/
noncomputable def leftStrictTransportScaffoldRestrictionEquivalence
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (relativeFunctorSpace q p)
      (relativeFunctorSpace q (simplicialReplacementProjection (leftStrictTransportDiagram p))) :=
  (relativeFunctorOverPre_isQCatEquivalence q (Over.homMk
    (U := Over.mk (simplicialReplacementProjection (leftStrictTransportDiagram p)))
    (V := Over.mk p) (universalScaffold p) (universalScaffold_projection p))
      (universalScaffold_isPrecompositionEquivalence p)).choose

/-- 概要：strict transport 間の strict な自然変換の空間から、元の相対 Hom へ戻す射。
方針：replacement 上の変換を scaffold で評価し、相対制限の同値の逆を合成する。
規約：全ての高次パラメーターに対する一つの単体集合の射を選ぶ。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の写像空間比較の片側の逆。 -/
noncomputable def leftStrictTransportMappingRetraction
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    strictDiagramMappingSpace (leftStrictTransportDiagram p) (leftStrictTransportDiagram q) ⟶
      relativeFunctorSpace q p :=
  strictDiagramMappingScaffoldMap (leftStrictTransportDiagram p) q ≫
    (leftStrictTransportScaffoldRestrictionEquivalence p q).inv

/-- 概要：相対射を strict transport の自然変換にして戻す合成は、相対 Hom 上の恒等と関手同型。
方針：評価と scaffold 前合成の厳密な可換性を、制限の同値の単位に合成する。
規約：選択した戻す射そのものについて、全次数のホモトピーを与える。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の写像空間比較の片側の逆条件。 -/
noncomputable def leftStrictTransportMappingRetraction_unitIso
    {C : Type u} [Category.{u} C] {E E' : SSet.{u}}
    (p : E ⟶ nerve C) (q : E' ⟶ nerve C) [LeftFibration p] [LeftFibration q] :
    FunctorIso (leftStrictTransportMappingSpaceMap p q ≫ leftStrictTransportMappingRetraction p q)
      (𝟙 (relativeFunctorSpace q p)) := by
  rw [leftStrictTransportMappingRetraction, ← Category.assoc,
    leftStrictTransportMappingSpaceMap_scaffold]
  exact (leftStrictTransportScaffoldRestrictionEquivalence p q).homInvIso

end SerrePositivity.InfinityCategories
