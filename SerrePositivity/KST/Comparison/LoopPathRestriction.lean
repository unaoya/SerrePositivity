module

public import SerrePositivity.KST.Comparison.BasedPathFamily
public import SerrePositivity.KST.Spectra.LoopPathFiber

/-!
# 標準ループ空間から基点始点 path space への制限

概要：二端点を潰す区間の商を使い、K-L9 の loop のファイバー表示の包含を記述する。
方針：二つの円の実際の同型と点つき内部 Hom の制限を合成する。
規約：Segal 1974 Proposition 1.5 の標準ループ写像とファイバー比較の一致への補助。
使われ方：円の商上の評価を区間上の評価へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial

/--
概要：基点を始点に取った区間から標準単体的円への商写像。
方針：終点も潰した円の表示から標準の円への同型を合成する。
規約：K-L9 の二つの円の同型をそのまま使う。
使われ方：loop から path への反変な制限。
-/
def intervalCircleProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} ⟶ PointedSimplicialSet.circle.{u} :=
  Spectra.pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint ≫ Spectra.endpointCircleIso.hom

/--
概要：区間から円への商写像の基礎射は境界を潰す元の商である。
方針：cofiber の射の普遍性の計算則を使う。
規約：局所化前の射の一致。
使われ方：既存の標準ループ写像の区間上の評価。
-/
theorem intervalCircleProjection_right : intervalCircleProjection.{u}.right =
    PointedObject.cofiberQuotient (SSet.boundary.{u} 1).ι := by
  change PointedObject.cofiberQuotient _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ≫
    Spectra.endpointCircleToCircle.{u}.right = _
  unfold Spectra.endpointCircleToCircle
  rw [PointedObject.cofiberQuotient_desc]

/--
概要：標準ループ空間から基点始点 path space への制限。
方針：区間の商を点つき内部 Hom へ反変に適用する。
規約：標的の Kan 性は不要。
使われ方：基点上の厳密なファイバーの包含。
-/
def loopPathRestriction (Y : PointedSimplicialSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right ⟶ (Spectra.basedPathSpace Y).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre intervalCircleProjection Y

/--
概要：loop の制限を基礎指数へ含めると、境界の商による通常の指数の制限になる。
方針：点つき内部 Hom の制限の包含の式と、区間の商の基礎射の一致を使う。
規約：パラメータ付きの全次数の写像の等式。
使われ方：標準ループ写像の評価との比較。
-/
@[reassoc] theorem loopPathRestriction_ι (Y : PointedSimplicialSet.{u}) :
    loopPathRestriction Y ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y =
      PointedObject.basedHomι PointedSimplicialSet.circle Y ≫
        (MonoidalClosed.pre
          (PointedObject.cofiberQuotient (SSet.boundary.{u} 1).ι)).app Y.right := by
  rw [loopPathRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, intervalCircleProjection_right]

end SerrePositivity.KST.Comparison
