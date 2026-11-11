module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardFaithful
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendExtractRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointHExt

/-!
# 元の後向き二列の対象の貼り戻しと両往復

概要：元の指定 Hom と残りの語を貼り戻し、全対象を同じ対象として回収する。
方針：元の接合点と両係数を端点の移送込みで照合する。
規約：元の切断関手と指定部分圏の実際の Hom を保持する。
使われ方：DK9.4・10.3の元の後向き分解の逆。

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
def backwardBackwardRebuild (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.property) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z)

lemma backwardBackwardRebuild_joint (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ Z := by
  apply WideSubcategory.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.property) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z)

lemma backwardBackwardRebuild_tail (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (W := W) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as.property
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj_obj H T
  have hh : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T)) := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T).symm rfl _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  exact hh.symm.trans (heq_of_eq he)

private lemma markedValue_heq {A B B' : C} (hB : B = B')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) A B) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) A B')
    (h : HEq S T) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value T)) := by
  cases hB
  cases h
  rfl
private lemma discrete_mk_heq {A B : Type u} {a : A} {b : B}
    (h : A = B) (hab : HEq a b) : HEq (Discrete.mk a) (Discrete.mk b) := by
  cases h
  cases hab
  rfl

lemma backwardBackwardRebuild_head (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardObject W w X Y
      (backwardBackwardRebuild W w X Y Z))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left _ _ Z).as
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (W := W) e.hom e.property
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right _ _ Z
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj_obj H T
  have hh : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.obj rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T)) := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T).symm _ _ ?_ ?_
    · intro j; rfl
    · intro i; rfl
  have hv := markedValue_heq W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.joint_eq H T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj H T)) H (hh.symm.trans (heq_of_eq he))
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value H) = e := by
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
lemma backwardBackwardRebuild_object (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardTarget W w X Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).obj (backwardBackwardRebuild W w X Y Z) = Z :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.objectEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardLeftCoefficient W X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardRightCoefficient W w Y)).injective
      (sigma_pair_ext _ _ (backwardBackwardRebuild_joint W w X Y Z)
        (backwardBackwardRebuild_head W w X Y Z) (backwardBackwardRebuild_tail W w X Y Z))
lemma backwardBackwardRebuild_functor_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardSource W w X Y) :
    backwardBackwardRebuild W w X Y ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).obj S) = S := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)).val (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)).property) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) = S
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.obj_value]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartRecovery.rebuilt_eq S
instance backwardBackwardFunctor_essSurj : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardBackwardFunctor W w X Y).EssSurj where
  mem_essImage Z := ⟨backwardBackwardRebuild W w X Y Z,
    ⟨eqToIso (backwardBackwardRebuild_object W w X Y Z)⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
