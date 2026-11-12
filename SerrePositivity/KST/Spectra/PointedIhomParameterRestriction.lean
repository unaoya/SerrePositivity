module

public import SerrePositivity.KST.Spectra.PointedIhomActionNaturality

/-!
概要：パラメータ評価の厳密な可換四角形を、同じ内部 Hom の作用と実区間へ移す。
方針：内部 Hom の二つの源自然性と同じ制限の合成則を使う。
規約：Kan 性・単射性不要。使われ方：次段の単位比較の制限と構造三角形の対角辺の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping
variable {K L E E' T V : PointedSimplicialSet.{u}}
  (i : L ⟶ K) (j : E' ⟶ E) (a : T ⟶ PointedObject.basedHom K E)
  (e : T ⟶ PointedObject.basedHom L E')
  (he : a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i E = e ≫ PointedObject.basedHomMap L j)
include he

/-- 同じ評価四角形は、全 Hom の射として内部 Hom の作用と制限の厳密四角形を与える。 -/
lemma ihomParameterAction_restrict :
    (ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a (PointedObject.basedHom K V)) ≫
      PointedObject.basedHomMap T (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V) =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V ≫ ihomAction L E' V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom L V) := by
  have hn := (MonoidalClosed.pre a).naturality (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  change (ihomAction K E V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a (PointedObject.basedHom K V)) ≫
    (ihom T).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V) = _
  rw [Category.assoc]
  erw [← hn]
  rw [← Category.assoc, ihomAction_restrict, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, he]
  rw [← Category.assoc]
  erw [ihomAction_pre L j V]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  rfl

/-- 実際の同じ区間を写す二つの経路も、元の同じ辺として厳密に一致する。 -/
lemma VerticalPath.basedIhomMap_parameter_restrict {f g : E ⟶ V}
    (H : VerticalPath (PointedObject.toPoint V) f g) :
    (((H.basedIhomMap K).pre a).basedPost (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)).path =
      (((H.pre j).basedIhomMap L).pre e).path := by
  have hm := congrArg Under.Hom.right (ihomParameterAction_restrict (V := V) i j a e he)
  have hp := congrArg (H.path ≫ ·) hm
  rw [VerticalPath.basedIhomMap_pre_path]
  change (((H.basedIhomMap K).pre a).path ≫
    (PointedObject.basedHomMap T (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i V)).right) = _
  rw [VerticalPath.basedIhomMap_pre_path]
  change _ = (H.path ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed j V).right) ≫
    (ihomAction L E' V ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed e (PointedObject.basedHom L V)).right
  simpa only [Under.comp_right, Category.assoc] using hp

end SerrePositivity.KST.Spectra.PointedMapping
