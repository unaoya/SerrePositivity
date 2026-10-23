module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackInputLimitCone
public import SerrePositivity.InfinityCategories.F2.CatInfinity.ArrowLimitConeExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PullbackLimitConeExistence

/-!
概要：選んだ両入力の極限錐を厳密に保つ lax pullback の極限錐の存在。
方針：両端で極限を持つ矢印図式の錐を入力の直積の錐へ合わせて貼る。
規約：元の図式と指定した両入力の全錐を保持する。
使われ方：Tamme Lemma 8 の極限の存在・射影の保存・逆方向の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：像も極限である両入力の指定極限錐を保つ lax pullback の極限錐が存在する。
方針：矢印圏の点ごとの極限の存在と引き戻しの像の厳密化を合成する。
規約：両射影との一致は頂点だけでなく全錐の等式。
使われ方：lax pullback の有限極限と射影の保存。 -/
lemma exists_limitCone_laxPullback_with_components {J A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (r : J ⟶ laxPullback p q)
    (ca : JoinCone (r ≫ laxPullbackFst p q)) (cb : JoinCone (r ≫ laxPullbackSnd p q))
    (ha : IsLimitCone ca) (hb : IsLimitCone cb)
    (hpa : IsLimitCone (mapJoinCone p ca)) (hqb : IsLimitCone (mapJoinCone q cb)) :
    ∃ c : JoinCone r, IsLimitCone c ∧ mapJoinCone (laxPullbackFst p q) c = ca ∧
      mapJoinCone (laxPullbackSnd p q) c = cb := by
  have : Quasicategory (A ⊗ B) := quasicategory_tensor A B
  have : Quasicategory (C ⊗ C) := quasicategory_tensor C C
  have h0 : HasLimit (evaluateFunctorDiagram (r ≫ laxPullbackArrow p q)
      (stdSimplex.obj₀Equiv.symm 0)) := by
    change HasLimit ((r ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    have he : (r ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        (r ≫ laxPullbackFst p q) ≫ p := by simp only [Category.assoc, laxPullbackArrow_source]
    rw [he]
    exact ⟨mapJoinCone p ca, hpa⟩
  have h1 : HasLimit (evaluateFunctorDiagram (r ≫ laxPullbackArrow p q)
      (stdSimplex.obj₀Equiv.symm 1)) := by
    change HasLimit ((r ≫ laxPullbackArrow p q) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1))
    have he : (r ≫ laxPullbackArrow p q) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
        (r ≫ laxPullbackSnd p q) ≫ q := by simp only [Category.assoc, laxPullbackArrow_target]
    rw [he]
    exact ⟨mapJoinCone q cb, hqb⟩
  obtain ⟨ce, he, hep⟩ := exists_limitCone_arrow_with_limit_image
    (r ≫ laxPullbackArrow p q) h0 h1
  obtain ⟨ci, hi, hiq, hif, his⟩ := exists_laxPullback_input_limitCone p q r ca cb ha hb hpa hqb
  obtain ⟨c, hc, _, hci⟩ := exists_limitCone_pullback_with_snd (arrowEndpointPair C) (p ⊗ₘ q)
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
