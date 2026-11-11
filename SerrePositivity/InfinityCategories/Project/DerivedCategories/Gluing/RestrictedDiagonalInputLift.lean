module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputPair
/-! # 元二入力を持つ同一対角引き戻しの普遍持ち上げ

概要：同じ対角の二合成対応と元二入力を、入力制限した二対応の引き戻しへ持ち上げる。
方針：入力対の二射影で二つの内側引き戻しを作り、共有対角で外側引き戻しへ入れる。
規約：四つの座標をすべて保持し、入力を忘れる射だけで比較しない。
使われ方：主比較の標的と入力付き模型の厳密な座標同型の普遍性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
variable {E F I J Q A B W : SSet.{u}} (p : E ⟶ I) (q : F ⟶ J)
  (d : E ⟶ Q) (e : F ⟶ Q) (a : A ⟶ I) (b : B ⟶ J)
  (s : W ⟶ pullback e d) (t : W ⟶ A ⊗ B)
  (h : s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair p q d e = t ≫ (a ⊗ₘ b))

include h in
lemma dgGluingRestrictedDiagonalInputLift_left_condition :
    (s ≫ pullback.snd e d) ≫ p = (t ≫ fst A B) ≫ a := by
  have he := congrArg (fun k => k ≫ fst I J) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair, Category.assoc,
    lift_fst, tensorHom_fst] using he

include h in
lemma dgGluingRestrictedDiagonalInputLift_right_condition :
    (s ≫ pullback.fst e d) ≫ q = (t ≫ snd A B) ≫ b := by
  have he := congrArg (fun k => k ≫ snd I J) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair, Category.assoc,
    lift_snd, tensorHom_snd] using he

def dgGluingRestrictedDiagonalInputLift :
    W ⟶ pullback (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) :=
  pullback.lift
    (pullback.lift (s ≫ pullback.snd e d) (t ≫ fst A B)
      (dgGluingRestrictedDiagonalInputLift_left_condition p q d e a b s t h))
    (pullback.lift (s ≫ pullback.fst e d) (t ≫ snd A B)
      (dgGluingRestrictedDiagonalInputLift_right_condition p q d e a b s t h)) (by
      simp only [Category.assoc, pullback.lift_fst_assoc]
      exact congrArg (fun k => s ≫ k) (pullback.condition (f := e) (g := d)).symm)

lemma dgGluingRestrictedDiagonalInputLift_forget :
    dgGluingRestrictedDiagonalInputLift p q d e a b s t h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b = s := by
  apply pullback.hom_ext <;>
    simp only [dgGluingRestrictedDiagonalInputLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget,
      Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

lemma dgGluingRestrictedDiagonalInputLift_inputs :
    dgGluingRestrictedDiagonalInputLift p q d e a b s t h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b = t := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingRestrictedDiagonalInputLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair,
      Category.assoc, lift_fst, lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullback.lift_snd]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
