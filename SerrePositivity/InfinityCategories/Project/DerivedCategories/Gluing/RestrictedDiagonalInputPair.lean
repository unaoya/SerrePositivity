module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalStrictForget
/-! # 同一対角の引き戻しで元二入力を保持する

概要：二入力で制限した合成対応の同一対角引き戻しを、元二入力とともに保持する。
方針：既存の忘却射の二射影と、二つの入力引き戻しの条件を比較する。
規約：対角と二入力の順序を明示し、入力を捨てない。
使われ方：入力付き模型と主比較の標的の厳密な座標同型を構成する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
variable {E F I J Q A B : SSet.{u}} (p : E ⟶ I) (q : F ⟶ J)
  (d : E ⟶ Q) (e : F ⟶ Q) (a : A ⟶ I) (b : B ⟶ J)

def dgGluingRestrictedDiagonalEndpointPair : pullback e d ⟶ I ⊗ J :=
  lift (pullback.snd e d ≫ p) (pullback.fst e d ≫ q)

def dgGluingRestrictedDiagonalInputPair :
    pullback (pullback.fst p a ≫ d) (pullback.fst q b ≫ e) ⟶ A ⊗ B :=
  lift (pullback.fst _ _ ≫ pullback.snd p a) (pullback.snd _ _ ≫ pullback.snd q b)

lemma dgGluingRestrictedDiagonalInputPair_condition :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget p q d e a b ≫
      dgGluingRestrictedDiagonalEndpointPair p q d e =
    dgGluingRestrictedDiagonalInputPair p q d e a b ≫ (a ⊗ₘ b) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingRestrictedDiagonalEndpointPair, dgGluingRestrictedDiagonalInputPair,
      Category.assoc, lift_fst, tensorHom_fst,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget_last p q d e a b]
    exact (congrArg (fun h => pullback.fst (pullback.fst p a ≫ d)
      (pullback.fst q b ≫ e) ≫ h) (pullback.condition (f := p) (g := a)))
  · simp only [dgGluingRestrictedDiagonalEndpointPair, dgGluingRestrictedDiagonalInputPair,
      Category.assoc, lift_snd, tensorHom_snd,
      reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalStrictForget_first p q d e a b]
    exact (congrArg (fun h => pullback.snd (pullback.fst p a ≫ d)
      (pullback.fst q b ≫ e) ≫ h) (pullback.condition (f := q) (g := b)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
