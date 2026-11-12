module

public import SerrePositivity.KST.Spectra.PointedPreActionCotensor
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary
public import SerrePositivity.KST.Spectra.DeloopedExchangeSquareCoordinates

/-!
概要：元の前合成区間は、同じ射の全パラメータ族による後合成と実辺全体で自然。
方針：cotensor 交換の豊穣等式を元の辺へ作用させ、転置した族への通常の自然性と合成する。
規約：区間を選び直さない。使われ方：普遍交換区間の源側の実辺の全族照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
variable {W D : PointedSimplicialSet.{u}} {a b : W ⟶ D}
  (R : VerticalPath (PointedObject.toPoint D) a b)

/-- 同じ前合成区間を cotensor に移すことと源交換は、実辺全体で厳密に可換。 -/
lemma basedPre_cotensor_exchange_path (P Z : PointedSimplicialSet.{u}) :
    ((R.basedPre (PointedObject.basedHom P Z)).basedPost
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom).path =
      (((R.basedPre Z).basedIhomMap P).pre (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom).path := by
  change (R.basedPre (PointedObject.basedHom P Z)).path ≫
      (PointedObject.basedHomMap (PointedObject.basedHom D (PointedObject.basedHom P Z))
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom).right =
    ((R.basedPre Z).basedIhomMap P).path ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom
        (PointedObject.basedHom P (PointedObject.basedHom W Z))).right
  rw [basedPre_action_path, basedIhomMap_path, basedPre_action_path]
  simpa only [Under.comp_right, Category.assoc] using
    congrArg (fun m => R.path ≫ m.right) (preAction_cotensor W D P Z)

/-- 同じ前合成区間は、射の全族による後合成に対して実辺全体で厳密に自然。 -/
lemma basedPre_parametricPost_path {P Z Z' : PointedSimplicialSet.{u}}
    (v : P ⟶ PointedObject.basedHom Z Z') :
    ((R.basedPre Z).basedPost (parametricPost W v)).path =
      (((R.basedPre Z').basedIhomMap P).pre (parametricPost D v)).path := by
  calc
    _ = (((R.basedPre Z).basedPost (PointedObject.basedHomMap W (transpose v))).basedPost
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z').hom).path := by
      rw [basedPost_basedPost_path, parametricPost_exchange]
    _ = (((R.basedPre (PointedObject.basedHom P Z')).pre
        (PointedObject.basedHomMap D (transpose v))).basedPost
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z').hom).path :=
      congrArg (· ≫ (PointedObject.basedHomMap (PointedObject.basedHom D Z)
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z').hom).right) (R.basedPre_post_path (transpose v))
    _ = (((R.basedPre (PointedObject.basedHom P Z')).basedPost
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z').hom).pre
          (PointedObject.basedHomMap D (transpose v))).path :=
      ((R.basedPre (PointedObject.basedHom P Z')).pre_basedPost_path
        (PointedObject.basedHomMap D (transpose v)) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z').hom).symm
    _ = ((((R.basedPre Z').basedIhomMap P).pre (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z').hom).pre
        (PointedObject.basedHomMap D (transpose v))).path :=
      congrArg (· ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.basedHomMap D (transpose v))
        (PointedObject.basedHom P (PointedObject.basedHom W Z'))).right)
        (R.basedPre_cotensor_exchange_path P Z')
    _ = _ := by rw [pre_pre_path, parametricPost_exchange]

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
