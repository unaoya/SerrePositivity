module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorLimitConeExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorLimitConeImage
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackProjections

/-!
概要：選んだ両入力の極限錐とその像から入力の直積の極限錐を作る。
方針：合成の括弧付けだけを移送し、元の全錐を保つ直積の存在定理を使う。
規約：元の両入力の全錐の射を厳密に保持する。
使われ方：lax pullback の極限錐の第二成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両入力と像の極限錐から、元の全錐を保つ入力の直積の極限錐が存在する。
方針：図式の合成を正規化し、直積の存在と像の成分判定を使う。
規約：底への像も極限錐である。
使われ方：選んだ入力を保つ lax pullback の極限錐。 -/
lemma exists_laxPullback_input_limitCone {J A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (r : J ⟶ laxPullback p q)
    (ca : JoinCone (r ≫ laxPullbackFst p q)) (cb : JoinCone (r ≫ laxPullbackSnd p q))
    (ha : IsLimitCone ca) (hb : IsLimitCone cb)
    (hpa : IsLimitCone (mapJoinCone p ca)) (hqb : IsLimitCone (mapJoinCone q cb)) :
    ∃ ci : JoinCone (r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)),
      IsLimitCone ci ∧ IsLimitCone (mapJoinCone (p ⊗ₘ q) ci) ∧
      ci.val ≫ fst A B = ca.val ∧ ci.val ≫ snd A B = cb.val := by
  let ca' : JoinCone ((r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ fst A B) :=
    ca.cast (Category.assoc _ _ _).symm
  let cb' : JoinCone ((r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ snd A B) :=
    cb.cast (Category.assoc _ _ _).symm
  obtain ⟨ci, hi, hif, his⟩ := exists_limitCone_tensor_with_components
    (r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ca' cb'
    (ha.cast _) (hb.cast _)
  have hf : ci.val ≫ fst A B = ca.val := congrArg Subtype.val hif
  have hs : ci.val ≫ snd A B = cb.val := congrArg Subtype.val his
  refine ⟨ci, hi, isLimitCone_tensorHom_of_component_images p q ci ?_ ?_, hf, hs⟩
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hpa
    change (ci.val ≫ fst A B) ≫ p = ca.val ≫ p
    rw [hf]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hqb
    change (ci.val ≫ snd A B) ≫ q = cb.val ≫ q
    rw [hs]

end SerrePositivity.InfinityCategories.F2
