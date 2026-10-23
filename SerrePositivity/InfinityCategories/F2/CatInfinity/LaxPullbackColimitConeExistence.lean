module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackInputColimitCone
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowColimitConeExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackColimitConeExistence

/-!
概要：選んだ両入力の余極限錐を厳密に保つ lax pullback の余極限錐の存在。
方針：両端で余極限を持つ矢印図式の錐を入力の直積の錐へ合わせて貼る。
規約：元の図式と指定した両入力の全余錐を保持する。
使われ方：Tamme Lemma 8 の余極限の存在・射影の保存・逆方向の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：像も余極限である両入力の指定余極限錐を保つ lax pullback の余極限錐が存在する。
方針：矢印圏の点ごとの余極限の存在と引き戻しの像の厳密化を合成する。
規約：両射影との一致は頂点だけでなく全余錐の等式。
使われ方：lax pullback の有限余極限と射影の保存。 -/
lemma exists_colimitCone_laxPullback_with_components {J A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (r : J ⟶ laxPullback p q)
    (ca : JoinCocone (r ≫ laxPullbackFst p q)) (cb : JoinCocone (r ≫ laxPullbackSnd p q))
    (ha : IsColimitCone ca) (hb : IsColimitCone cb)
    (hpa : IsColimitCone (F1B.kanPostcomposeCocone p ca))
    (hqb : IsColimitCone (F1B.kanPostcomposeCocone q cb)) :
    ∃ c : JoinCocone r, IsColimitCone c ∧ F1B.kanPostcomposeCocone (laxPullbackFst p q) c = ca ∧
      F1B.kanPostcomposeCocone (laxPullbackSnd p q) c = cb := by
  have : Quasicategory (A ⊗ B) := quasicategory_tensor A B
  have : Quasicategory (C ⊗ C) := quasicategory_tensor C C
  have h0 : HasColimit (evaluateFunctorDiagram (r ≫ laxPullbackArrow p q)
      (stdSimplex.obj₀Equiv.symm 0)) := by
    change HasColimit ((r ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    have he : (r ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        (r ≫ laxPullbackFst p q) ≫ p := by simp only [Category.assoc, laxPullbackArrow_source]
    rw [he]
    exact ⟨F1B.kanPostcomposeCocone p ca, hpa⟩
  have h1 : HasColimit (evaluateFunctorDiagram (r ≫ laxPullbackArrow p q)
      (stdSimplex.obj₀Equiv.symm 1)) := by
    change HasColimit ((r ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1))
    have he : (r ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
        (r ≫ laxPullbackSnd p q) ≫ q := by simp only [Category.assoc, laxPullbackArrow_target]
    rw [he]
    exact ⟨F1B.kanPostcomposeCocone q cb, hqb⟩
  obtain ⟨ce, he, hep⟩ := exists_colimitCone_arrow_with_colimit_image
    (r ≫ laxPullbackArrow p q) h0 h1
  obtain ⟨ci, hi, hiq, hif, his⟩ := exists_laxPullback_input_colimitCone p q r ca cb ha hb hpa hqb
  obtain ⟨c, hc, _, hci⟩ := exists_colimitCone_pullback_with_snd (arrowEndpointPair C) (p ⊗ₘ q)
    (arrowEndpointPair_kanEquivalenceLifting C) r ce ci he hep hi hiq
  have hcv : c.val ≫ pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) = ci.val :=
    congrArg Subtype.val hci
  refine ⟨c, hc, ?_, ?_⟩
  · apply Subtype.ext
    change c.val ≫ (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) ≫ fst A B) = ca.val
    rw [← Category.assoc, hcv, hif]
  · apply Subtype.ext
    change c.val ≫ (pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) ≫ snd A B) = cb.val
    rw [← Category.assoc, hcv, his]

end SerrePositivity.InfinityCategories.F2
