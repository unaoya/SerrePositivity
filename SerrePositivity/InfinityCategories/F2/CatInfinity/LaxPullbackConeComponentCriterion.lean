module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackProjections

/-!
概要：lax pullback 内の指定錐の極限性を両入力とその像から得る。
方針：矢印圏と直積の成分判定を厳密な引き戻しの錐族の判定へ渡す。
規約：元の錐の矢印成分と両射影を保持する。
使われ方：Tamme Lemma 8 の有限極限と安定性への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両入力とその像が極限錐である lax pullback 内の錐は極限錐。
方針：指定矢印の両端の等式で像の錐を照合し、三成分の極限判定を使う。
規約：元の二関手には全極限の保存を仮定しない。
使われ方：lax pullback の有限極限と射影の保存の構成。 -/
lemma isLimitCone_laxPullback_of_components {J A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) {r : J ⟶ laxPullback p q} (c : JoinCone r)
    (ha : IsLimitCone (mapJoinCone (laxPullbackFst p q) c))
    (hb : IsLimitCone (mapJoinCone (laxPullbackSnd p q) c))
    (hp : IsLimitCone (mapJoinCone p (mapJoinCone (laxPullbackFst p q) c)))
    (hq : IsLimitCone (mapJoinCone q (mapJoinCone (laxPullbackSnd p q) c))) :
    IsLimitCone c := by
  have : Quasicategory (A ⊗ B) := quasicategory_tensor A B
  have : Quasicategory (C ⊗ C) := quasicategory_tensor C C
  let ca := mapJoinCone (laxPullbackArrow p q) c
  have h0 : IsLimitCone (evaluateFunctorCone ca (stdSimplex.obj₀Equiv.symm 0)) := by
    apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hp
    change (c.val ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = (c.val ≫ laxPullbackFst p q) ≫ p
    simp only [Category.assoc, laxPullbackArrow_source]
  have h1 : IsLimitCone (evaluateFunctorCone ca (stdSimplex.obj₀Equiv.symm 1)) := by
    apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hq
    change (c.val ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = (c.val ≫ laxPullbackSnd p q) ≫ q
    simp only [Category.assoc, laxPullbackArrow_target]
  apply isLimitCone_pullback_of_components (arrowEndpointPair C) (p ⊗ₘ q) c
  · exact isLimitCone_arrow_of_endpoints ca h0 h1
  · apply isLimitCone_tensor_of_components
    · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 ha
      change (c.val ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ fst A B =
        c.val ≫ (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) ≫ fst A B)
      exact Category.assoc _ _ _
    · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hb
      change (c.val ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ snd A B =
        c.val ≫ (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) ≫ snd A B)
      exact Category.assoc _ _ _
  · apply isLimitCone_tensor_of_components
    · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 h0
      change ((c.val ≫ laxPullbackArrow p q) ≫ arrowEndpointPair C) ≫ fst C C =
        (c.val ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
      rw [Category.assoc, arrowEndpointPair, lift_fst]
    · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 h1
      change ((c.val ≫ laxPullbackArrow p q) ≫ arrowEndpointPair C) ≫ snd C C =
        (c.val ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)
      rw [Category.assoc, arrowEndpointPair, lift_snd]

end SerrePositivity.InfinityCategories.F2
