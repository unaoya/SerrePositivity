module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSections

/-!
概要：全空間の図式の錐から、分類図式と頂点の共変 Hom の間の全自然な射を構成する。
方針：元の錐を coslice へ curry し、その底変換への全空間比較を分類する。
規約：各点の射を独立に選ばず、同じ全錐から一つの関手圏の射を作る。
使われ方：全解錐が与える余表現可能関手への retract の一方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {E B C : SSet.{u}} [Quasicategory B] [Quasicategory C]
  (p : E ⟶ B) [LeftFibration p] (i : B ⟶ C) (c : JoinCone (p ≫ i))

/-- 概要：全解の錐を元の頂点の coslice の底変換へ写す。
方針：錐の coslice 切断と元の射影を引き戻しに束ねる。
規約：元の全空間 E と元の底 B を保持する。
使われ方：全分類関手への Hom 比較射の幾何的な始域。 -/
def coneClassificationOver :
    E ⟶ pullback (sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)) i :=
  pullback.lift (coherentConeCosliceSection c) p (coherentConeCosliceSection_projection c)

/-- 概要：全解錐から作った coslice 比較は元の射影を厳密に被覆する。
方針：引き戻しの第二射影の式を使う。
規約：射影は元の p そのもの。
使われ方：元の比較を分類関手の射に送る底条件。 -/
lemma coneClassificationOver_projection :
    coneClassificationOver p i c ≫
      pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)) i = p :=
  pullback.lift_snd _ _ _

/-- 概要：全解錐は、元の分類図式から錐頂点の全共変 Hom 制限への自然な射を与える。
方針：coslice 底変換への比較を分類し、底変換と共変 Hom の全比較同型を合成する。
規約：元の全関手間の射であり、各点の写像の族だけではない。
使われ方：accessible 関手を表現可能関手の retract として構成する比較。 -/
def coneClassificationHom :
    FunctorHom (leftStraighteningInfinityDiagram p)
      ((SSet.uliftFunctor.{u + 1, u}).map i ≫ covariantRepresentableInfinity c.vertex) := by
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex)
  have : LeftFibration (pullback.snd q i) :=
    ⟨leftFibrations.pullback_snd q i (LeftFibration.mem (p := q))⟩
  exact leftClassificationHom p (pullback.snd q i) (coneClassificationOver p i c)
      (coneClassificationOver_projection p i c) ≫
    (leftStraighteningInfinityDiagram_baseChangeIso q i).inv ≫
    (FunctorIso.precomp (Compact.covariantRepresentableInfinity_cosliceIso c.vertex)
      ((SSet.uliftFunctor.{u + 1, u}).map i)).inv

end SerrePositivity.InfinityCategories.F2.Presentable
