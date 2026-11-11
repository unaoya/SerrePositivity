module

public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostComposition
public import SerrePositivity.KST.Spectra.RawSpectrumPointedPostLifting
public import SerrePositivity.KST.Spectra.PointedTrivialVerticalPaths
public import SerrePositivity.KST.Spectra.PointedRelativeTransposeHomotopy

/-!
概要：選択済みの levelwiseInverse の左右逆則を、元の全 Hom の実区間として構成する。
方針：mapping path 列の源射影の上で同じ像を持つ族を垂直に結び、終点へ後合成する。
規約：段の成分一致から全列ホモトピーを推論しない。
使われ方：元の loop 比較と signedLoopUnit の全 Hom 接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open RawSpectrumMapping
variable (A : OmegaSpectrum.{u}) {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
  (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right)

/-- 選択済み逆射の右逆区間の元になる、mapping path の源射影上の同じ実垂直区間。 -/
def levelwiseInverse_post_right_lift_interval :
    PointedMapping.VerticalPath
      (pointedPost A (KanSequence.mappingPathSource (sequenceHom f)))
      (pointedPost A (sequenceHom (levelwiseInverse f hf)) ≫
        pointedPost A (KanSequence.mappingPathComparison (sequenceHom f)))
      (pointedPost A (inversePathSection f hf)) := by
  let r := KanSequence.mappingPathSource (sequenceHom f)
  let u := KanSequence.mappingPathComparison (sequenceHom f)
  let s := inversePathSection f hf
  let g := sequenceHom (levelwiseInverse f hf)
  have hur : pointedPost A u ≫ pointedPost A r = 𝟙 _ :=
    pointedPost_comp_id A u r (KanSequence.mappingPathComparison_source (sequenceHom f))
  have hsr : pointedPost A s ≫ pointedPost A r = pointedPost A g :=
    pointedPost_comp_eq A s r g (fun _ => rfl)
  have h : (pointedPost A g ≫ pointedPost A u) ≫ pointedPost A r =
      pointedPost A s ≫ pointedPost A r := by
    rw [Category.assoc, hur, Category.comp_id, hsr]
  exact PointedMapping.verticalPathOfRlp (pointedPost A r)
    (pointedPost_rlp A r (KanSequence.mappingPathSource_rlp (sequenceHom f)))
    (pointedPost A g ≫ pointedPost A u) (pointedPost A s) h

/-- 同じ選択済み逆射の右合成は、任意の BF 源の元の全 Hom で恒等射へ実際に変形する。 -/
def levelwiseInverse_post_right_interval :
    PointedMapping.VerticalPath (PointedObject.toPoint (pointedSpace A Y.toKanSequence))
      (pointedPost A (sequenceHom (levelwiseInverse f hf)) ≫ pointedPost A (sequenceHom f))
      (𝟙 (pointedSpace A Y.toKanSequence)) := by
  let p := KanSequence.mappingPathTarget (sequenceHom f)
  let u := KanSequence.mappingPathComparison (sequenceHom f)
  let s := inversePathSection f hf
  let g := sequenceHom (levelwiseInverse f hf)
  have hup : pointedPost A u ≫ pointedPost A p = pointedPost A (sequenceHom f) :=
    pointedPost_comp_eq A u p (sequenceHom f)
      (KanSequence.mappingPathComparison_target (sequenceHom f))
  have hsp : pointedPost A s ≫ pointedPost A p = 𝟙 _ :=
    pointedPost_comp_id A s p (inversePathSection_target f hf)
  have ha : (pointedPost A g ≫ pointedPost A u) ≫ pointedPost A p =
      pointedPost A g ≫ pointedPost A (sequenceHom f) := by rw [Category.assoc, hup]
  exact ((levelwiseInverse_post_right_lift_interval A f hf).forgetProjection.basedPost
    (pointedPost A p)).changeEndpoints ha.symm hsp.symm

/-- 右逆区間全体は、同じ垂直持ち上げ区間への元の mapping path 終点射の後合成。 -/
lemma levelwiseInverse_post_right_interval_h :
    (levelwiseInverse_post_right_interval A f hf).homotopy.h =
      (levelwiseInverse_post_right_lift_interval A f hf).homotopy.h ≫
        (pointedPost A (KanSequence.mappingPathTarget (sequenceHom f))).right := by
  rw [levelwiseInverse_post_right_interval,
    PointedMapping.VerticalPath.changeEndpoints_homotopy_h,
    PointedMapping.VerticalPath.basedPost_homotopy_h]
  rw [PointedMapping.VerticalPath.homotopy_h, PointedMapping.VerticalPath.homotopy_h]
  rfl

/-- 同じ選択済み逆射の左合成も、元の全 Hom の恒等射へ基点固定で実際に変形する。 -/
def levelwiseInverse_post_left_interval :
    PointedMapping.VerticalPath (PointedObject.toPoint (pointedSpace A X.toKanSequence))
      (pointedPost A (sequenceHom f) ≫ pointedPost A (sequenceHom (levelwiseInverse f hf)))
      (𝟙 (pointedSpace A X.toKanSequence)) := by
  let r := KanSequence.mappingPathSource (sequenceHom f)
  let p := KanSequence.mappingPathTarget (sequenceHom f)
  let u := KanSequence.mappingPathComparison (sequenceHom f)
  let s := inversePathSection f hf
  let g := sequenceHom (levelwiseInverse f hf)
  have hsp : pointedPost A s ≫ pointedPost A p = 𝟙 _ :=
    pointedPost_comp_id A s p (inversePathSection_target f hf)
  have hup : pointedPost A u ≫ pointedPost A p = pointedPost A (sequenceHom f) :=
    pointedPost_comp_eq A u p (sequenceHom f)
      (KanSequence.mappingPathComparison_target (sequenceHom f))
  have h : (pointedPost A (sequenceHom f) ≫ pointedPost A s) ≫ pointedPost A p =
      pointedPost A u ≫ pointedPost A p := by
    rw [Category.assoc, hsp, Category.comp_id, hup]
  let H := PointedMapping.verticalPathOfRlp (pointedPost A p)
    (pointedPost_rlp A p (inversePathTarget_rlp f hf))
    (pointedPost A (sequenceHom f) ≫ pointedPost A s) (pointedPost A u) h
  have hsr : pointedPost A s ≫ pointedPost A r = pointedPost A g :=
    pointedPost_comp_eq A s r g (fun _ => rfl)
  have hur : pointedPost A u ≫ pointedPost A r = 𝟙 _ :=
    pointedPost_comp_id A u r (KanSequence.mappingPathComparison_source (sequenceHom f))
  have ha : (pointedPost A (sequenceHom f) ≫ pointedPost A s) ≫ pointedPost A r =
      pointedPost A (sequenceHom f) ≫ pointedPost A g := by rw [Category.assoc, hsr]
  exact (H.forgetProjection.basedPost (pointedPost A r)).changeEndpoints ha.symm hur.symm

end SerrePositivity.KST.Spectra.OmegaSpectrum
