module

public import SerrePositivity.KST.Spectra.OriginalLoopModelMap
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInversePostInterval
public import SerrePositivity.KST.Spectra.SignedLoopSourcePostComparison
public import SerrePositivity.KST.Spectra.LeftVerticalBasedComposition

/-!
概要：源の twist を経由した全 Hom 比較を、元の signedLoopUnit の後合成族へ接続する。
方針：選択済み逆射の全 Hom の右逆区間を前合成し、同じ源比較区間と指定した射影三角形で貼る。
規約：元の選択済み逆射と単位を保持する。Kan 随伴の構造区間との比較は別工程。
使われ方：HA §1.4.2。元の evaluationPost と BF 単位の全パラメータ比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping
variable (A X : OmegaSpectrum.{u})

/-- 選択済み originalLoopModelMap を元の比較へ戻すと、全 Hom で元の単位へ実際に変形する。 -/
def originalLoopModelMap_unit_post_interval :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace A (signedLoopModel X).toKanSequence))
      (pointedPost A (sequenceHom (originalLoopModelMap X)) ≫
        pointedPost A (sequenceHom (signedLoopComparison X)))
      (pointedPost A (sequenceHom (signedLoopUnit X))) := by
  let v := pointedPost A (sequenceHom (signedLoopUnit X))
  let g := pointedPost A (sequenceHom
    (levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)))
  let e := pointedPost A (sequenceHom (signedLoopComparison X))
  have hv : v ≫ g = pointedPost A (sequenceHom (originalLoopModelMap X)) :=
    pointedPost_comp_eq A (sequenceHom (signedLoopUnit X))
      (sequenceHom (levelwiseInverse (signedLoopComparison X) (signedLoopComparison_levelwise X)))
      (sequenceHom (originalLoopModelMap X)) (fun _ => rfl)
  have ha : pointedPost A (sequenceHom (originalLoopModelMap X)) ≫ e = v ≫ (g ≫ e) := by
    rw [← hv, Category.assoc]
  exact ((levelwiseInverse_post_right_interval A (signedLoopComparison X)
    (signedLoopComparison_levelwise X)).pre v).changeEndpoints ha (Category.comp_id v).symm

/-- 二つの元の区間を、逆射側の同じ射影トレース全体を指定して貼る。 -/
def signedLoopSourceUnitPostSpecifiedComposite :
    PointedMapping.LeftVerticalBasedComposite
      ((signedLoopSourceComparison_post_interval A X).pre
        (pointedPost A (sequenceHom (originalLoopModelMap X))))
      (originalLoopModelMap_unit_post_interval A X) := by
  apply PointedMapping.LeftVerticalBasedComposite.choose
  intro U V i hi
  exact (pointedPost_rlp A (signedLoopProjection X)
    (fun n => (KanSequence.replacementStage
      (KanSequence.signedLoopTail X.toKanSequence) n).projection_rlp)) i
      (SSet.modelCategoryQuillen.J_le_monomorphisms i hi)

/-- 同じ二辺と実三角形を保持する合成。底の三角形も上の選択で厳密に指定される。 -/
def signedLoopSourceUnitPostComposite :
    PointedMapping.BasedPathComposite
      (((signedLoopSourceComparison_post_interval A X).pre
        (pointedPost A (sequenceHom (originalLoopModelMap X)))).forgetProjection)
      (originalLoopModelMap_unit_post_interval A X) :=
  (signedLoopSourceUnitPostSpecifiedComposite A X).composite

/-- 元の単位までの同じ合成区間。二つの元の辺との実三角形は上の名前つき選択に保持する。 -/
def signedLoopSourceUnitPostInterval :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (pointedSpace A (signedLoopModel X).toKanSequence))
      (pointedPost A (sequenceHom (originalLoopModelMap X)) ≫
        pointedPost A
          (sequenceHom (signedLoopSourceTwistComparison X ≫ signedLoopSourceComparison X)))
      (pointedPost A (sequenceHom (signedLoopUnit X))) :=
  (signedLoopSourceUnitPostComposite A X).path

/-- 対角区間の raw 射影は、選択済み逆射の同じトレースに厳密に一致する。 -/
lemma signedLoopSourceUnitPostInterval_projection_path :
    (signedLoopSourceUnitPostInterval A X).path ≫
      (PointedObject.basedHomMap (pointedSpace A X.toKanSequence)
        (pointedPost A (signedLoopProjection X))).right =
    (originalLoopModelMap_unit_post_interval A X).path ≫
      (PointedObject.basedHomMap (pointedSpace A X.toKanSequence)
        (pointedPost A (signedLoopProjection X))).right :=
  (signedLoopSourceUnitPostSpecifiedComposite A X).path_over

end SerrePositivity.KST.Spectra.OmegaSpectrum
