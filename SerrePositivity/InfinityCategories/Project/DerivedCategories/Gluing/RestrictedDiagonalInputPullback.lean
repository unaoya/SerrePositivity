module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputLift
/-! # 元二入力を保持する同一対角模型の厳密な座標同型

概要：入力制限した二合成対応の引き戻しを、元同一対角模型を二入力で引き戻したものと同定する。
方針：四座標での一意性と元二入力を保つ普遍持ち上げから極限錐を構成する。
規約：忘却射だけで同値性を主張せず、二入力の組を同時に保存する。
使われ方：入力付き模型の実逆射を主比較の標的へ厳密に輸送する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
variable {E F I J Q A B W : SSet.{u}} (p : E ⟶ I) (q : F ⟶ J)
  (d : E ⟶ Q) (e : F ⟶ Q) (a : A ⟶ I) (b : B ⟶ J)

lemma dgGluingRestrictedDiagonalInput_hom_ext
    (m n : W ⟶ pullback (pullback.fst p a ≫ d) (pullback.fst q b ≫ e))
    (hs : m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b =
      n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b)
    (ht : m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b =
      n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b) : m = n := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have h := congrArg (fun k => k ≫ pullback.snd e d) hs
      simpa only [Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget_last p q d e a b] using h
    · have h := congrArg (fun k => k ≫ fst A B) ht
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair, Category.assoc, lift_fst] using h
  · apply pullback.hom_ext
    · have h := congrArg (fun k => k ≫ pullback.fst e d) hs
      simpa only [Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget_first p q d e a b] using h
    · have h := congrArg (fun k => k ≫ snd A B) ht
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair, Category.assoc, lift_snd] using h

def dgGluingRestrictedDiagonalInputCone :
    PullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair p q d e) (a ⊗ₘ b) :=
  PullbackCone.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair_condition p q d e a b)

def dgGluingRestrictedDiagonalInputCone_isLimit :
    IsLimit (dgGluingRestrictedDiagonalInputCone p q d e a b) :=
  PullbackCone.IsLimit.mk _
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputLift p q d e a b s.fst s.snd s.condition)
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputLift_forget p q d e a b s.fst s.snd s.condition)
    (fun s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputLift_inputs p q d e a b s.fst s.snd s.condition)
    (fun s m hs ht => dgGluingRestrictedDiagonalInput_hom_ext p q d e a b m _
      (hs.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputLift_forget p q d e a b
        s.fst s.snd s.condition).symm)
      (ht.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputLift_inputs p q d e a b
        s.fst s.snd s.condition).symm))

lemma dgGluingRestrictedDiagonalInput_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair p q d e) (a ⊗ₘ b) :=
  IsPullback.of_isLimit (dgGluingRestrictedDiagonalInputCone_isLimit p q d e a b)

def dgGluingRestrictedDiagonalInputIso :
    pullback (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair p q d e) (a ⊗ₘ b) :=
  (dgGluingRestrictedDiagonalInput_isPullback p q d e a b).isoPullback

lemma dgGluingRestrictedDiagonalInputIso_forget :
    (dgGluingRestrictedDiagonalInputIso p q d e a b).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b :=
  (dgGluingRestrictedDiagonalInput_isPullback p q d e a b).isoPullback_hom_fst

lemma dgGluingRestrictedDiagonalInputIso_inputs :
    (dgGluingRestrictedDiagonalInputIso p q d e a b).hom ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalInputPair p q d e a b :=
  (dgGluingRestrictedDiagonalInput_isPullback p q d e a b).isoPullback_hom_snd
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
