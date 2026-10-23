module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorColimitConeExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorColimitConeImage
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackProjections

/-!
概要：選んだ両入力の余極限錐とその像から入力の直積の余極限錐を作る。
方針：合成の括弧付けだけを移送し、元の全余錐を保つ直積の存在定理を使う。
規約：元の両入力の全余錐の射を厳密に保持する。
使われ方：lax pullback の余極限錐の第二成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両入力と像の余極限錐から、元の全余錐を保つ入力の直積の余極限錐が存在する。
方針：図式の合成を正規化し、直積の存在と像の成分判定を使う。
規約：底への像も余極限錐である。
使われ方：選んだ入力を保つ lax pullback の余極限錐。 -/
lemma exists_laxPullback_input_colimitCone {J A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (r : J ⟶ laxPullback p q)
    (ca : JoinCocone (r ≫ laxPullbackFst p q)) (cb : JoinCocone (r ≫ laxPullbackSnd p q))
    (ha : IsColimitCone ca) (hb : IsColimitCone cb)
    (hpa : IsColimitCone (F1B.kanPostcomposeCocone p ca))
    (hqb : IsColimitCone (F1B.kanPostcomposeCocone q cb)) :
    ∃ ci : JoinCocone (r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)),
      IsColimitCone ci ∧ IsColimitCone (F1B.kanPostcomposeCocone (p ⊗ₘ q) ci) ∧
      ci.val ≫ fst A B = ca.val ∧ ci.val ≫ snd A B = cb.val := by
  let ca' : JoinCocone ((r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ fst A B) :=
    ⟨ca.val, ca.property.trans (Category.assoc _ _ _).symm⟩
  let cb' : JoinCocone ((r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ≫ snd A B) :=
    ⟨cb.val, cb.property.trans (Category.assoc _ _ _).symm⟩
  obtain ⟨ci, hi, hif, his⟩ := exists_colimitCone_tensor_with_components
    (r ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q)) ca' cb'
    ((isColimitCone_iff_of_cocone_val_eq ca' ca rfl).2 ha)
    ((isColimitCone_iff_of_cocone_val_eq cb' cb rfl).2 hb)
  have hf : ci.val ≫ fst A B = ca.val := congrArg Subtype.val hif
  have hs : ci.val ≫ snd A B = cb.val := congrArg Subtype.val his
  refine ⟨ci, hi, isColimitCone_tensorHom_of_component_images p q ci ?_ ?_, hf, hs⟩
  · apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).2 hpa
    change (ci.val ≫ fst A B) ≫ p = ca.val ≫ p
    rw [hf]
  · apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).2 hqb
    change (ci.val ≫ snd A B) ≫ q = cb.val ≫ q
    rw [hs]

end SerrePositivity.InfinityCategories.F2
