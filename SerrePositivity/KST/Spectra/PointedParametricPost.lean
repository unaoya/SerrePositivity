module

public import SerrePositivity.KST.Spectra.PointedIhomActionNaturality
public import SerrePositivity.KST.Spectra.PointedPrecompositionNaturality

/-!
概要：射の族による内部 Hom の後合成を、パラメータを内部 Hom に保つ一つの射で表す。
方針：同じ ihomAction を転置し、源制限との豊穣自然性を厳密に計算する。
規約：パラメータに Kan 性を要求しない。使われ方：全族に対する普遍延長切断の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 射の同じ族を全入力へ後合成する、転置した内部 Hom の実作用。 -/
def parametricPost (A : PointedSimplicialSet.{u}) {P Z Z' : PointedSimplicialSet.{u}}
    (v : P ⟶ PointedObject.basedHom Z Z') :
    PointedObject.basedHom A Z ⟶
      PointedObject.basedHom P (PointedObject.basedHom A Z') :=
  transpose (v ≫ ihomAction A Z Z')

/-- 同じ射の族による後合成は、源制限と全パラメータを含め厳密に可換。 -/
lemma parametricPost_restrict {A' A P Z Z' : PointedSimplicialSet.{u}} (i : A' ⟶ A)
    (v : P ⟶ PointedObject.basedHom Z Z') :
    parametricPost A v ≫ PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z') =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z ≫ parametricPost A' v := by
  have hh := ihomAction_restrict i Z Z'
  change ihomAction A Z Z' ≫
      PointedObject.basedHomMap (PointedObject.basedHom A Z) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z') =
    ihomAction A' Z Z' ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z) (PointedObject.basedHom A' Z') at hh
  have h : (v ≫ ihomAction A Z Z') ≫
      PointedObject.basedHomMap (PointedObject.basedHom A Z) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z') =
    (v ≫ ihomAction A' Z Z') ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z) (PointedObject.basedHom A' Z') := by
    simpa only [Category.assoc] using congrArg (v ≫ ·) hh
  have ht := congrArg transpose h
  have hl := transpose_post (v ≫ ihomAction A Z Z') (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z')
  have hr := @transpose_pre_inner P (PointedObject.basedHom A' Z)
    (PointedObject.basedHom A Z) (PointedObject.basedHom A' Z')
    (v ≫ ihomAction A' Z Z') (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z)
  exact hl.symm.trans (ht.trans hr)

end SerrePositivity.KST.Spectra.PointedMapping
