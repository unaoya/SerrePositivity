module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendExtractRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointHExt

/-!
# 元の前向き切断の対象の貼り戻しと両往復

概要：元の二方向 Grothendieck 圏の各対象を先頭列と残りで貼り戻す。
方針：元の接合点と両係数を端点の移送込みで回収する。
規約：元の切断関手を保ち、対象の両往復と本質的全射性を証明する。
使われ方：DK9.4・10.3の元の分解の逆。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
def forwardForwardRebuild (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z)

lemma forwardForwardRebuild_joint (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ Z := by
  apply WideSubcategory.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z)

lemma forwardForwardRebuild_tail (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj_obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z)
  have hh : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z)) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (forwardForwardRebuild W w X Y Z)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (forwardForwardRebuild W w X Y Z)) := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z)).symm rfl _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  exact hh.symm.trans (heq_of_eq he)

private lemma discrete_mk_heq {A B : Type u} {a : A} {b : B}
    (h : A = B) (hab : HEq a b) : HEq (Discrete.mk a) (Discrete.mk b) := by
  cases h
  cases hab
  rfl

lemma forwardForwardRebuild_head (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z).as
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z
  have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj_obj H T)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value_obj] at he
  have hh : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T))) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
  apply discrete_mk_heq
    (congrArg (fun A : C => X ⟶ A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T))
  exact hh.symm.trans (heq_of_eq he)

private lemma sigma_pair_ext {I : Type u} {A B : I → Type u}
    (x y : Σ i, A i × B i) (hi : x.1 = y.1)
    (ha : HEq x.2.1 y.2.1) (hb : HEq x.2.2 y.2.2) : x = y := by
  rcases x with ⟨i, a, b⟩
  rcases y with ⟨j, a', b'⟩
  cases hi
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl
lemma forwardForwardRebuild_object (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardTarget W w X Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).obj (forwardForwardRebuild W w X Y Z) = Z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.objectEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardLeftCoefficient W w Y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardRightCoefficient W X)).injective
      (sigma_pair_ext _ _ (forwardForwardRebuild_joint W w X Y Z)
        (forwardForwardRebuild_tail W w X Y Z) (forwardForwardRebuild_head W w X Y Z))
lemma forwardForwardRebuild_functor_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardSource W w X Y) :
    forwardForwardRebuild W w X Y ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).obj S) = S := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) = S
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.obj_value]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartRecovery.rebuilt_eq S

instance forwardForwardFunctor_essSurj : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardFunctor W w X Y).EssSurj where
  mem_essImage Z := ⟨forwardForwardRebuild W w X Y Z,
    ⟨eqToIso (forwardForwardRebuild_object W w X Y Z)⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
