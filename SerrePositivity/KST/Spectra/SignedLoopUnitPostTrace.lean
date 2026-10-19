module

public import SerrePositivity.KST.Spectra.SignedLoopUnitPostFactor

/-!
概要：元の BF 単位までの同じ全 Hom 区間の raw 射影を、選択済み逆射の実トレースで計算する。
方針：指定した底の合成三角形と、名前つき mapping path 垂直区間の評価式を使う。
規約：逆射側のトレースが定数とは主張しない。
使われ方：Kan 随伴比較の元の非零境界トレースとの照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping
variable (A X : OmegaSpectrum.{u})

/-- 同じ二辺の合成三角形の raw 射影全体。底は第二辺の同じトレースと恒等辺の合成。 -/
lemma signedLoopSourceUnitPostTriangle_projection :
    SSet.yonedaEquiv.symm (signedLoopSourceUnitPostComposite A X).triangle.simplex ≫
      (PointedObject.basedHomMap (pointedSpace A X.toKanSequence)
        (pointedPost A (signedLoopProjection X))).right =
    SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp
      ((originalLoopModelMap_unit_post_interval A X).edge.map
        (PointedObject.basedHomMap (pointedSpace A X.toKanSequence)
          (pointedPost A (signedLoopProjection X))).right)).simplex :=
  (signedLoopSourceUnitPostSpecifiedComposite A X).triangle_over

/-- 合成対角区間の raw 射影は、第二辺の同じ実トレースに厳密一致する。 -/
lemma signedLoopSourceUnitPostInterval_projection_h :
    (signedLoopSourceUnitPostInterval A X).homotopy.h ≫
      (pointedPost A (signedLoopProjection X)).right =
    (originalLoopModelMap_unit_post_interval A X).homotopy.h ≫
      (pointedPost A (signedLoopProjection X)).right :=
  (signedLoopSourceUnitPostSpecifiedComposite A X).homotopy_over

/-- 逆射側の同じ区間全体は、元の単位族と名前つき垂直区間・終点射の合成。 -/
lemma originalLoopModelMap_unit_post_interval_h :
    (originalLoopModelMap_unit_post_interval A X).homotopy.h =
    (pointedPost A (sequenceHom (signedLoopUnit X))).right ▷ (Δ[1] : SSet.{u}) ≫
      (levelwiseInverse_post_right_lift_interval A (signedLoopComparison X)
        (signedLoopComparison_levelwise X)).homotopy.h ≫
      (pointedPost A (KanSequence.mappingPathTarget
        (sequenceHom (signedLoopComparison X)))).right := by
  rw [originalLoopModelMap_unit_post_interval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.pre_homotopy_h, levelwiseInverse_post_right_interval_h]

/-- 単位までの対角区間の raw 射影を、同じ選択済み逆射の全パラメータの実トレースで計算。 -/
lemma signedLoopSourceUnitPostInterval_trace :
    (signedLoopSourceUnitPostInterval A X).homotopy.h ≫
      (pointedPost A (signedLoopProjection X)).right =
    (pointedPost A (sequenceHom (signedLoopUnit X))).right ▷ (Δ[1] : SSet.{u}) ≫
      (levelwiseInverse_post_right_lift_interval A (signedLoopComparison X)
        (signedLoopComparison_levelwise X)).homotopy.h ≫
      (pointedPost A (KanSequence.mappingPathTarget
        (sequenceHom (signedLoopComparison X)))).right ≫
      (pointedPost A (signedLoopProjection X)).right := by
  rw [signedLoopSourceUnitPostInterval_projection_h, originalLoopModelMap_unit_post_interval_h]
  simp only [Category.assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum
