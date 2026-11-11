module

public import SerrePositivity.KST.Spectra.UniversalSourceParametricSections
public import SerrePositivity.KST.Spectra.UniversalSourceIntervalNaturality
public import SerrePositivity.KST.Spectra.PointedIhomIntervalNaturality

/-!
概要：射の全パラメータ族の切断比較を、元の普遍区間に作用させた実正方形。
方針：同じ普遍区間をパラメータ内部 Hom へ移し、射影固定の入力比較を作用させる。
規約：全パラメータと元の普遍区間を保持。使われ方：普遍交換の族自然性の辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.UniversalSourceInterval
variable (I : UniversalSourceInterval.{u})

/-- 同じ普遍区間を全パラメータ内部 Hom へ移し、同じ単位制限を経由する形に表示する。 -/
def parametricFactoredInterval (P Z' : PointedSimplicialSet.{u}) :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom P (PointedObject.basedHom I.source Z')))
      (parametricRestriction I P Z' ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z'))
      (parametricRestriction I P Z' ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z')) := by
  have hs : parametricRestriction I P Z' ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z') =
    (ihom P).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z' ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z') :=
      (Functor.map_comp (ihom P) _ _).symm
  have ht : parametricRestriction I P Z' ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z') =
    (ihom P).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.unit Z' ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z') :=
      (Functor.map_comp (ihom P) _ _).symm
  exact ((factoredUniversalInterval I Z').basedIhomMap P).changeEndpoints hs ht

/-- 因子表示はパラメータ内部 Hom に移した同じ実辺全体を変更しない。 -/
lemma parametricFactoredInterval_path (P Z' : PointedSimplicialSet.{u}) :
    (parametricFactoredInterval I P Z').path =
      ((factoredUniversalInterval I Z').basedIhomMap P).path := rfl

variable {P Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : P ⟶ PointedObject.basedHom Z Z')

/-- 同じ全族切断比較を、同じ普遍区間のパラメータ内部 Hom 像へ作用させた実正方形。 -/
def parametricInputSquare :=
  PointedMapping.VerticalPath.inputSquare (parametricSectionComparison I v)
    (parametricFactoredInterval I P Z')

/-- 左境界全体は、元の同じ射の族と第一源作用の合成頂点で一定。 -/
lemma parametricInputSquare_start :
    SquareAdjustment.leftSide ≫ (parametricInputSquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedMapping.parametricPost I.source v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.first Z'))) := by
  change SquareAdjustment.leftSide ≫
    (PointedMapping.VerticalPath.inputSquare (parametricSectionComparison I v)
      (parametricFactoredInterval I P Z')).h = _
  rw [PointedMapping.VerticalPath.inputSquare_start_factored, parametricExtensionLeft_projection]

/-- 右境界全体も、元の同じ射の族と第二源作用の合成頂点で一定。 -/
lemma parametricInputSquare_finish :
    SquareAdjustment.rightSide ≫ (parametricInputSquare I v).h =
      SSet.const (PointedMapping.familyVertex (PointedMapping.parametricPost I.source v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed I.second Z'))) := by
  change SquareAdjustment.rightSide ≫
    (PointedMapping.VerticalPath.inputSquare (parametricSectionComparison I v)
      (parametricFactoredInterval I P Z')).h = _
  rw [PointedMapping.VerticalPath.inputSquare_finish_factored, parametricExtensionLeft_projection]

omit [KanComplex Z.right] in
/-- 標的側の元の区間を内部 Hom へ移しても、同じ切断を移した入力への制限。 -/
lemma parametricInterval_path :
    ((interval I Z').basedIhomMap P).path =
      ((parametricFactoredInterval I P Z').pre
        (PointedObject.basedHomMap P (extensionSection I Z'))).path := by
  change ((I.path.basedPre Z').path ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (extensionSection I Z')
      (PointedObject.basedHom I.source Z')).right) ≫
        (PointedMapping.ihomAction P (PointedObject.basedHom I.source Z')
          (PointedObject.basedHom I.source Z')).right =
    ((I.path.basedPre Z').path ≫
      (PointedMapping.ihomAction P (PointedObject.basedHom I.target Z')
        (PointedObject.basedHom I.source Z')).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap P (extensionSection I Z'))
        (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right
  have h := PointedMapping.ihomAction_pre P (extensionSection I Z')
    (PointedObject.basedHom I.source Z')
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (extensionSection I Z')
      (PointedObject.basedHom I.source Z') ≫
        PointedMapping.ihomAction P (PointedObject.basedHom I.source Z')
          (PointedObject.basedHom I.source Z') =
    PointedMapping.ihomAction P (PointedObject.basedHom I.target Z')
      (PointedObject.basedHom I.source Z') ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap P (extensionSection I Z'))
          (PointedObject.basedHom P (PointedObject.basedHom I.source Z')) at h
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun m => (I.path.basedPre Z').path ≫ m.right) h

omit [KanComplex Z.right] in
/-- 終辺は標的側の元の区間の内部 Hom 像へ同じ後合成族を前合成した辺そのもの。 -/
lemma parametricInput_one :
    (((interval I Z').basedIhomMap P).pre (PointedMapping.parametricPost I.source v)).path =
      ((parametricFactoredInterval I P Z').pre (parametricExtensionRight I v)).path := by
  change ((interval I Z').basedIhomMap P).path ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedMapping.parametricPost I.source v)
      (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right =
    (parametricFactoredInterval I P Z').path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (parametricExtensionRight I v)
        (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right
  rw [parametricInterval_path]
  change ((parametricFactoredInterval I P Z').path ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap P (extensionSection I Z'))
      (PointedObject.basedHom P (PointedObject.basedHom I.source Z'))).right) ≫ _ = _
  dsimp only [parametricExtensionRight]
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun q => (parametricFactoredInterval I P Z').path ≫ q.right)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp (PointedMapping.parametricPost I.source v)
        (PointedObject.basedHomMap P (extensionSection I Z'))
        (PointedObject.basedHom P (PointedObject.basedHom I.source Z')))

end SerrePositivity.KST.Spectra.UniversalSourceInterval
