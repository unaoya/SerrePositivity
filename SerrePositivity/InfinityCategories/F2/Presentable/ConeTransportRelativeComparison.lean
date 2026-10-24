module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoslicePointTransportComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSections
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices

/-!
概要：元の全解錐の各脚による標準輸送は元の全解図式と相対関手空間で同型。
方針：元の全空間の頂点の coslice 上の比較を同じ全錐の切断で前合成する。
規約：比較は全図式と同じ底を固定した相対 Hom の同型。
使われ方：分類した解関手の retract の分裂等式を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {A E B : SSet.{u}} (p : E ⟶ B)
  {f : A ⟶ E} (c : JoinCone f)

/-- 概要：元の全解錐の脚を底の指定頂点の coslice へ同時に写す。
方針：全空間の coslice 切断を元の射影で後合成する。
規約：同じ全解頂点を始点とする全ての脚を保持する。
使われ方：底上の表現可能関手への全空間比較。 -/
def conePointComparison :
    A ⟶ sliceUnder (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex)) :=
  coherentConeCosliceSection c ≫
    stableCoslicePostcomp (SSet.yonedaEquiv.symm c.vertex) p
      (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex))
      (SSet.yonedaEquiv_symm_comp c.vertex p)

/-- 概要：底の coslice への全脚比較は元の全解図式の底を厳密に保つ。
方針：正規化済み後合成と錐の coslice 切断の射影公式を使う。
規約：元の底の全射 f ≫ p。
使われ方：底を保つ分類比較の条件。 -/
lemma conePointComparison_projection :
    conePointComparison p c ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) c.vertex)) = f ≫ p := by
  rw [conePointComparison, Category.assoc, stableCoslicePostcomp_projection,
    ← Category.assoc, coherentConeCosliceSection_projection]

variable [Quasicategory B] [LeftFibration p]

/-- 概要：同じ全錐の脚に沿う標準輸送は元の全図式と相対関手空間で同型。
方針：頂点の coslice 上の比較を元の錐の全切断で前合成する。
規約：元の図式の全高次単体と底を保持する。
使われ方：全解関手を表現可能関手の retract にする恒等関係。 -/
def coneTransportRelativeComparison :
    VertexIso (relativeFunctorVertex p (f ≫ p) f rfl)
      (relativeFunctorVertex p (f ≫ p)
        (conePointComparison p c ≫ cosliceVertexTransport p c.vertex)
        (by rw [Category.assoc, cosliceVertexTransport_projection,
          conePointComparison_projection])) := by
  let a := sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) ≫ p
  let j : CategoryTheory.Over.mk (f ≫ p) ⟶ CategoryTheory.Over.mk a :=
    Over.homMk (coherentConeCosliceSection c) (by
      change coherentConeCosliceSection c ≫
        (sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) ≫ p) = f ≫ p
      rw [← Category.assoc, coherentConeCosliceSection_projection])
  have h := VertexIso.map (cosliceVertexTransportComparison p c.vertex)
    (relativeFunctorOverPre p j)
  erw [relativeFunctorOverPre_vertex p j _ _, relativeFunctorOverPre_vertex p j _ _] at h
  simpa only [j, Over.homMk_left, Over.mk_hom, coherentConeCosliceSection_projection,
    conePointComparison, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2.Presentable
