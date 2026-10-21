module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardFaithful
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendExtractRecovery
public import SerrePositivity.EInfinity.Hammock.ZigzagEndpointHExt

/-!
# 元の後向き二列の対象の貼り戻しと両往復

概要：元の指定 Hom と残りの語を貼り戻し、全対象を同じ対象として回収する。
方針：元の接合点と両係数を端点の移送込みで照合する。
規約：元の切断関手と指定部分圏の実際の Hom を保持する。
使われ方：DK9.4・10.3の元の後向き分解の逆。
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
def backwardBackwardRebuild (Z : backwardBackwardTarget W w X Y) : backwardBackwardSource W w X Y :=
  ZigzagAppend.obj (BackwardZigzag.obj (TwoSidedGrothendieck.left _ _ Z).as.hom
    (TwoSidedGrothendieck.left _ _ Z).as.property) (TwoSidedGrothendieck.right _ _ Z)

lemma backwardBackwardRebuild_joint (Z : backwardBackwardTarget W w X Y) :
    TwoSidedGrothendieck.base _ _ (backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z)) = TwoSidedGrothendieck.base _ _ Z := by
  apply WideSubcategory.ext
  exact ZigzagAppend.Part.joint_eq
    (BackwardZigzag.obj (TwoSidedGrothendieck.left _ _ Z).as.hom
      (TwoSidedGrothendieck.left _ _ Z).as.property) (TwoSidedGrothendieck.right _ _ Z)

lemma backwardBackwardRebuild_tail (Z : backwardBackwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.right _ _ (backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z))) (TwoSidedGrothendieck.right _ _ Z) := by
  let H := BackwardZigzag.obj (W := W) (TwoSidedGrothendieck.left _ _ Z).as.hom
    (TwoSidedGrothendieck.left _ _ Z).as.property
  let T := TwoSidedGrothendieck.right _ _ Z
  have he := ZigzagAppend.Part.rightObj_obj H T
  have hh : HEq (Zigzag.EndpointChange.obj (ZigzagAppend.Part.joint_eq H T) rfl
      (ZigzagAppend.Part.rightObj (ZigzagAppend.obj H T)))
      (ZigzagAppend.Part.rightObj (ZigzagAppend.obj H T)) := by
    refine Zigzag.object_hext_endpoints (ZigzagAppend.Part.joint_eq H T).symm rfl _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  exact hh.symm.trans (heq_of_eq he)

private lemma markedValue_heq {A B B' : C} (hB : B = B')
    (S : Zigzag W (Word.single .backward) A B) (T : Zigzag W (Word.single .backward) A B')
    (h : HEq S T) :
    HEq (BackwardZigzag.markedHomEquiv (BackwardZigzag.value S))
      (BackwardZigzag.markedHomEquiv (BackwardZigzag.value T)) := by
  cases hB
  cases h
  rfl
private lemma discrete_mk_heq {A B : Type u} {a : A} {b : B}
    (h : A = B) (hab : HEq a b) : HEq (Discrete.mk a) (Discrete.mk b) := by
  cases h
  cases hab
  rfl

lemma backwardBackwardRebuild_head (Z : backwardBackwardTarget W w X Y) :
    HEq (TwoSidedGrothendieck.left _ _ (backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z))) (TwoSidedGrothendieck.left _ _ Z) := by
  let e := (TwoSidedGrothendieck.left _ _ Z).as
  let H := BackwardZigzag.obj (W := W) e.hom e.property
  let T := TwoSidedGrothendieck.right _ _ Z
  have he := ZigzagAppend.Part.leftObj_obj H T
  have hh : HEq (Zigzag.EndpointChange.obj rfl (ZigzagAppend.Part.joint_eq H T)
      (ZigzagAppend.Part.leftObj (ZigzagAppend.obj H T)))
      (ZigzagAppend.Part.leftObj (ZigzagAppend.obj H T)) := by
    refine Zigzag.object_hext_endpoints rfl (ZigzagAppend.Part.joint_eq H T).symm _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  have hv := markedValue_heq W (ZigzagAppend.Part.joint_eq H T)
    (ZigzagAppend.Part.leftObj (ZigzagAppend.obj H T)) H (hh.symm.trans (heq_of_eq he))
  have hH : BackwardZigzag.markedHomEquiv (BackwardZigzag.value H) = e := by
    apply WideSubcategory.hom_ext
    change (𝟙 _) ≫ e.hom ≫ (𝟙 _) = e.hom
    simp only [Category.id_comp, Category.comp_id]
  apply discrete_mk_heq (congrArg (fun A : WideSubcategory W => A ⟶ (⟨X⟩ : WideSubcategory W))
    (backwardBackwardRebuild_joint W w X Y Z))
  exact hv.trans (heq_of_eq hH)

private lemma sigma_pair_ext {I : Type u} {A B : I → Type u}
    (x y : Σ i, A i × B i) (hi : x.1 = y.1)
    (ha : HEq x.2.1 y.2.1) (hb : HEq x.2.2 y.2.2) : x = y := by
  rcases x with ⟨i, a, b⟩
  rcases y with ⟨j, a', b'⟩
  cases hi
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl
lemma backwardBackwardRebuild_object (Z : backwardBackwardTarget W w X Y) :
    (backwardBackwardFunctor W w X Y).obj (backwardBackwardRebuild W w X Y Z) = Z :=
  (TwoSidedGrothendieck.objectEquiv (backwardLeftCoefficient W X)
    (backwardRightCoefficient W w Y)).injective
      (sigma_pair_ext _ _ (backwardBackwardRebuild_joint W w X Y Z)
        (backwardBackwardRebuild_head W w X Y Z) (backwardBackwardRebuild_tail W w X Y Z))
lemma backwardBackwardRebuild_functor_obj (S : backwardBackwardSource W w X Y) :
    backwardBackwardRebuild W w X Y ((backwardBackwardFunctor W w X Y).obj S) = S := by
  change ZigzagAppend.obj (BackwardZigzag.obj (BackwardZigzag.value
    (ZigzagAppend.Part.leftObj S)).val (BackwardZigzag.value
    (ZigzagAppend.Part.leftObj S)).property) (ZigzagAppend.Part.rightObj S) = S
  rw [BackwardZigzag.obj_value]
  exact ZigzagAppend.Part.rebuilt_eq S
instance backwardBackwardFunctor_essSurj : (backwardBackwardFunctor W w X Y).EssSurj where
  mem_essImage Z := ⟨backwardBackwardRebuild W w X Y Z,
    ⟨eqToIso (backwardBackwardRebuild_object W w X Y Z)⟩⟩
end SerrePositivity.EInfinity.Hammock.FirstColumn
