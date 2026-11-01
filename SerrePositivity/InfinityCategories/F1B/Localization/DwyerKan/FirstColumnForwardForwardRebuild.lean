module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendExtractRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointHExt

/-!
# 元の前向き切断の対象の貼り戻しと両往復

概要：元の二方向 Grothendieck 圏の各対象を先頭列と残りで貼り戻す。
方針：元の接合点と両係数を端点の移送込みで回収する。
規約：元の切断関手を保ち、対象の両往復と本質的全射性を証明する。
使われ方：DK9.4・10.3の元の分解の逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
def forwardForwardRebuild (Z : forwardForwardTarget W w X Y) : forwardForwardSource W w X Y :=
  ZigzagAppend.obj (ForwardZigzag.obj (TwoSidedGrothendieck.right _ _ Z).as)
    (TwoSidedGrothendieck.left _ _ Z)

lemma forwardForwardRebuild_joint (Z : forwardForwardTarget W w X Y) :
    TwoSidedGrothendieck.base _ _ (forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z)) = TwoSidedGrothendieck.base _ _ Z := by
  apply WideSubcategory.ext
  exact ZigzagAppend.Part.joint_eq
    (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as)
    (TwoSidedGrothendieck.left _ _ Z)

lemma forwardForwardRebuild_tail (Z : forwardForwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.left _ _ (forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z))) (TwoSidedGrothendieck.left _ _ Z) := by
  have he := ZigzagAppend.Part.rightObj_obj
    (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as)
    (TwoSidedGrothendieck.left _ _ Z)
  have hh : HEq (Zigzag.EndpointChange.obj
      (ZigzagAppend.Part.joint_eq
        (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as)
        (TwoSidedGrothendieck.left _ _ Z)) rfl
      (ZigzagAppend.Part.rightObj (forwardForwardRebuild W w X Y Z)))
      (ZigzagAppend.Part.rightObj (forwardForwardRebuild W w X Y Z)) := by
    refine Zigzag.object_hext_endpoints
      (ZigzagAppend.Part.joint_eq
        (ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as)
        (TwoSidedGrothendieck.left _ _ Z)).symm rfl _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  exact hh.symm.trans (heq_of_eq he)

private lemma discrete_mk_heq {A B : Type u} {a : A} {b : B}
    (h : A = B) (hab : HEq a b) : HEq (Discrete.mk a) (Discrete.mk b) := by
  cases h
  cases hab
  rfl

lemma forwardForwardRebuild_head (Z : forwardForwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.right _ _ (forwardForwardObject W w X Y
      (forwardForwardRebuild W w X Y Z))) (TwoSidedGrothendieck.right _ _ Z) := by
  let H := ForwardZigzag.obj (W := W) (TwoSidedGrothendieck.right _ _ Z).as
  let T := TwoSidedGrothendieck.left _ _ Z
  have he := congrArg ForwardZigzag.value (ZigzagAppend.Part.leftObj_obj H T)
  rw [ForwardZigzag.value_obj] at he
  have hh : HEq (ForwardZigzag.value (Zigzag.EndpointChange.obj rfl
      (ZigzagAppend.Part.joint_eq H T) (ZigzagAppend.Part.leftObj (ZigzagAppend.obj H T))))
      (ForwardZigzag.value (ZigzagAppend.Part.leftObj (ZigzagAppend.obj H T))) := by
    dsimp only [ForwardZigzag.value, Zigzag.EndpointChange.obj]
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
  apply discrete_mk_heq
    (congrArg (fun A : C => X ⟶ A) (ZigzagAppend.Part.joint_eq H T))
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
lemma forwardForwardRebuild_object (Z : forwardForwardTarget W w X Y) :
    (forwardForwardFunctor W w X Y).obj (forwardForwardRebuild W w X Y Z) = Z :=
  (TwoSidedGrothendieck.objectEquiv (forwardLeftCoefficient W w Y)
    (forwardRightCoefficient W X)).injective
      (sigma_pair_ext _ _ (forwardForwardRebuild_joint W w X Y Z)
        (forwardForwardRebuild_tail W w X Y Z) (forwardForwardRebuild_head W w X Y Z))
lemma forwardForwardRebuild_functor_obj (S : forwardForwardSource W w X Y) :
    forwardForwardRebuild W w X Y ((forwardForwardFunctor W w X Y).obj S) = S := by
  change ZigzagAppend.obj (ForwardZigzag.obj (ForwardZigzag.value
    (ZigzagAppend.Part.leftObj S))) (ZigzagAppend.Part.rightObj S) = S
  rw [ForwardZigzag.obj_value]
  exact ZigzagAppend.Part.rebuilt_eq S

instance forwardForwardFunctor_essSurj : (forwardForwardFunctor W w X Y).EssSurj where
  mem_essImage Z := ⟨forwardForwardRebuild W w X Y Z,
    ⟨eqToIso (forwardForwardRebuild_object W w X Y Z)⟩⟩
end SerrePositivity.EInfinity.Hammock.FirstColumn
