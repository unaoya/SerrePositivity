module

public import SerrePositivity.KST.Spectra.PointedPrecompositionInterval
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：源の実区間・実二単体を前合成へ移す単一の内部 Hom 射。
方針：普遍評価への後合成とパラメータ交換を一つの射に束ねる。
規約：区間や充填を選び直さない。使われ方：源単位の指定三角形の全パラメータ像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 源射を、その射による内部 Hom の前合成へ送る実際の点つき射。 -/
def preAction (W D C : PointedSimplicialSet.{u}) :
    PointedObject.basedHom W D ⟶
      PointedObject.basedHom (PointedObject.basedHom D C) (PointedObject.basedHom W C) :=
  PointedObject.basedHomMap W (transpose (𝟙 (PointedObject.basedHom D C))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W (PointedObject.basedHom D C) C).hom

/-- 指定した入力族へ作用する同じ前合成の射。 -/
def preParameterAction {W D C A T : PointedSimplicialSet.{u}}
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) :
    PointedObject.basedHom W D ⟶
      PointedObject.basedHom T (PointedObject.basedHom W C) :=
  preAction W D C ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a (PointedObject.basedHom W C)

/-- 同じ入力への前合成は、転置した入力への後合成と交換で厳密に表示できる。 -/
lemma preAction_restrict {W D C A : PointedSimplicialSet.{u}}
    (r : A ⟶ PointedObject.basedHom D C) :
    preAction W D C ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r (PointedObject.basedHom W C) =
      PointedObject.basedHomMap W (transpose r) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W A C).hom := by
  have ht : transpose (𝟙 (PointedObject.basedHom D C)) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r C =
      transpose r := by
    have h := congrArg transpose
      (transpose_pre_inner (transpose (𝟙 (PointedObject.basedHom D C))) r)
    simpa only [transpose_transpose, Category.comp_id] using h
  have hn := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right W r C
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, PointedObject.ihom_obj_eq_basedHom] at hn
  unfold preAction
  rw [Category.assoc, ← hn, ← Category.assoc]
  change ((ihom W).map (transpose (𝟙 (PointedObject.basedHom D C))) ≫
    (ihom W).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed r C)) ≫ _ = _
  rw [← Functor.map_comp, ht]
  rfl

/-- 恒等パラメータの同じ作用は、入力への後合成と転置の単一の射に一致する。 -/
lemma preParameterAction_id {W D C A : PointedSimplicialSet.{u}}
    (r : A ⟶ PointedObject.basedHom D C) :
    preParameterAction (W := W) r (𝟙 A) =
      PointedObject.basedHomMap W (transpose r) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W A C).hom := by
  have hid : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (𝟙 A) (PointedObject.basedHom W C) = 𝟙 _ := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact congrArg (fun t => t.app (PointedObject.basedHom W C)) (MonoidalClosed.pre_id A)
  rw [preParameterAction, hid, Category.comp_id]
  exact preAction_restrict r

/-- 任意の入力族についても、同じ前合成作用は転置した入力への後合成で表せる。 -/
lemma preParameterAction_eq_post {W D C A T : PointedSimplicialSet.{u}}
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) :
    preParameterAction (W := W) r a =
      PointedObject.basedHomMap W (transpose (a ≫ r)) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W T C).hom := by
  rw [preParameterAction, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  exact preAction_restrict (a ≫ r)

namespace VerticalPath

/-- 前合成の実区間は、元の辺全体を単一の前合成射へ写したもの。 -/
lemma basedPre_action_path {W D : PointedSimplicialSet.{u}} {f g : W ⟶ D}
    (H : VerticalPath (PointedObject.toPoint D) f g) (C : PointedSimplicialSet.{u}) :
    (H.basedPre C).path = H.path ≫ (preAction W D C).right := by
  change (H.path ≫ _) ≫ _ = H.path ≫ (_ ≫ _)
  exact Category.assoc _ _ _

/-- 全パラメータへの源作用も、同じ射による元の辺そのものの像。 -/
lemma basedPreAction_action_path {W D C A T : PointedSimplicialSet.{u}}
    {f g : W ⟶ D} (H : VerticalPath (PointedObject.toPoint D) f g)
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) :
    (H.basedPreAction r a).path = H.path ≫ (preParameterAction (W := W) r a).right := by
  change ((H.basedPre C).path ≫ _) ≫ _ = _
  rw [basedPre_action_path]
  simp only [preParameterAction, Under.comp_right, Category.assoc]

/-- 全パラメータの前合成区間は、同じ入力への後合成・転置と辺全体で一致する。 -/
lemma basedPreAction_post_transpose_path {W D C A T : PointedSimplicialSet.{u}}
    {f g : W ⟶ D} (H : VerticalPath (PointedObject.toPoint D) f g)
    (r : A ⟶ PointedObject.basedHom D C) (a : T ⟶ A) :
    (H.basedPreAction r a).path =
      ((H.basedPost (transpose (a ≫ r))).basedTranspose).path := by
  rw [basedPreAction_action_path, preParameterAction_eq_post]
  change H.path ≫ (_ ≫ _) = (H.path ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

end VerticalPath
end SerrePositivity.KST.Spectra.PointedMapping
