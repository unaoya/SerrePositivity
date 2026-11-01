module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardBackwardFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendExtractRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointHExt

/-!
# 元の混合二方向の切断の対象の貼り戻しと両往復

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
def forwardBackwardRebuild (Z : forwardBackwardTarget W w X Y) : forwardBackwardSource W w X Y :=
  ZigzagAppend.obj (ForwardZigzag.obj ((TwoSidedGrothendieck.right _ _ Z).1).as)
    ((TwoSidedGrothendieck.right _ _ Z).2)

lemma forwardBackwardRebuild_joint (Z : forwardBackwardTarget W w X Y) :
    TwoSidedGrothendieck.base _ _ (forwardBackwardObject W w X Y
      (forwardBackwardRebuild W w X Y Z)) = TwoSidedGrothendieck.base _ _ Z := by
  apply WideSubcategory.ext
  exact ZigzagAppend.Part.joint_eq
    (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as)
    ((TwoSidedGrothendieck.right _ _ Z).2)

lemma forwardBackwardRebuild_tail (Z : forwardBackwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.right _ _ (forwardBackwardObject W w X Y
      (forwardBackwardRebuild W w X Y Z))).2 ((TwoSidedGrothendieck.right _ _ Z).2) := by
  have he := ZigzagAppend.Part.rightObj_obj
    (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as)
    ((TwoSidedGrothendieck.right _ _ Z).2)
  have hh : HEq (Zigzag.EndpointChange.obj
      (ZigzagAppend.Part.joint_eq
        (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as)
        ((TwoSidedGrothendieck.right _ _ Z).2)) rfl
      (ZigzagAppend.Part.rightObj (forwardBackwardRebuild W w X Y Z)))
      (ZigzagAppend.Part.rightObj (forwardBackwardRebuild W w X Y Z)) := by
    refine Zigzag.object_hext_endpoints
      (ZigzagAppend.Part.joint_eq
        (ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as)
        ((TwoSidedGrothendieck.right _ _ Z).2)).symm rfl _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  exact hh.symm.trans (heq_of_eq he)

private lemma discrete_mk_heq {A B : Type u} {a : A} {b : B}
    (h : A = B) (hab : HEq a b) : HEq (Discrete.mk a) (Discrete.mk b) := by
  cases h
  cases hab
  rfl

lemma forwardBackwardRebuild_head (Z : forwardBackwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.right _ _ (forwardBackwardObject W w X Y
      (forwardBackwardRebuild W w X Y Z))).1 ((TwoSidedGrothendieck.right _ _ Z).1) := by
  let H := ForwardZigzag.obj (W := W) ((TwoSidedGrothendieck.right _ _ Z).1).as
  let T := (TwoSidedGrothendieck.right _ _ Z).2
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
lemma forwardBackwardRebuild_object (Z : forwardBackwardTarget W w X Y) :
    (forwardBackwardFunctor W w X Y).obj (forwardBackwardRebuild W w X Y Z) = Z :=
  (TwoSidedGrothendieck.objectEquiv CoefficientProduct.point
    (forwardBackwardRightCoefficient W w X Y)).injective
      (sigma_pair_ext _ _ (forwardBackwardRebuild_joint W w X Y Z)
        (heq_of_eq (Subsingleton.elim (α := Discrete PUnit.{u + 1}) _ _))
        (CoefficientProduct.pair_heq (forwardBackwardRebuild_head W w X Y Z)
          (forwardBackwardRebuild_tail W w X Y Z)))
lemma forwardBackwardRebuild_functor_obj (S : forwardBackwardSource W w X Y) :
    forwardBackwardRebuild W w X Y ((forwardBackwardFunctor W w X Y).obj S) = S := by
  change ZigzagAppend.obj (ForwardZigzag.obj (ForwardZigzag.value
    (ZigzagAppend.Part.leftObj S))) (ZigzagAppend.Part.rightObj S) = S
  rw [ForwardZigzag.obj_value]
  exact ZigzagAppend.Part.rebuilt_eq S

instance forwardBackwardFunctor_essSurj : (forwardBackwardFunctor W w X Y).EssSurj where
  mem_essImage Z := ⟨forwardBackwardRebuild W w X Y Z,
    ⟨eqToIso (forwardBackwardRebuild_object W w X Y Z)⟩⟩
end SerrePositivity.EInfinity.Hammock.FirstColumn
