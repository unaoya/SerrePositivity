module

public import SerrePositivity.KST.Spectra.PointedPreActionComposition
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeCurriedComposition

/-!
概要：元の前合成作用を cotensor へ移す操作と、同じ二つの内部 Hom の交換を照合する。
方針：合成と交換の全パラメータ式を curry・転置し、同じ三つの豊穣作用へ戻す。
規約：頂点での等式に還元しない。使われ方：普遍区間の源辺の全族自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 前合成と cotensor 交換は、元の同じ豊穣作用の射として全単体で厳密に可換。 -/
lemma preAction_cotensor (W D P Z : PointedSimplicialSet.{u}) :
    preAction W D (PointedObject.basedHom P Z) ≫
        PointedObject.basedHomMap (PointedObject.basedHom D (PointedObject.basedHom P Z))
          (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom =
      preAction W D Z ≫ ihomAction P (PointedObject.basedHom D Z) (PointedObject.basedHom W Z) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom
          (PointedObject.basedHom P (PointedObject.basedHom W Z)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.curriedComposition W D P Z
  rw [← ihomAction_eq_curry_comp, ← ihomAction_eq_curry_comp] at h
  change ihomAction W D (PointedObject.basedHom P Z) ≫
      PointedObject.basedHomMap (PointedObject.basedHom W D)
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom ≫ PointedObject.basedHomMap P (ihomAction W D Z) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso P (PointedObject.basedHom W D) (PointedObject.basedHom W Z)).hom at h
  have hp := parametricPost_exchange P (preAction W D Z)
  rw [transpose_preAction] at hp
  rw [← hp] at h
  have ht := congrArg transpose h
  have hl := transpose_post (ihomAction W D (PointedObject.basedHom P Z))
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso W P Z).hom
  have hr := transpose_pre_outer (parametricPost P (preAction W D Z))
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso D P Z).hom
  rw [parametricPost, transpose_transpose] at hr
  rw [preAction_eq_transpose_ihomAction W D (PointedObject.basedHom P Z)]
  exact hl.symm.trans (ht.trans (hr.trans (Category.assoc _ _ _)))

end SerrePositivity.KST.Spectra.PointedMapping
