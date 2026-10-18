module

public import SerrePositivity.InfinityCategories.F1.CoherentResolutionFaceUnion

/-!
概要：有限個の面の和上で解像の射影は前合成による同値を与える。
方針：面族の濃度について強い帰納法を使い、一枚の面と残りの和を交わりに沿って貼り合わせる。
規約：全ての面と空の面族を含む。
使われ方：Kerodon Proposition 4.6.7.23、境界上の比較の有限帰納法。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：各面は射影で同じ頂点集合の標準単体の面へ写る。
方針：各段の最大元は台に属することを使う。
規約：部分複体の制限条件として述べる。
使われ方：Kerodon Proposition 4.6.7.23、制限射の貼り合わせの入力。 -/
lemma coherentResolutionFace_mapsTo {n : ℕ} (T : Finset (Fin (n + 1))) :
    coherentResolutionFace.{u} T ≤ (stdSimplex.face T).preimage (coherentResolutionProjection n) := by
  intro d F hF
  change Finset.univ.image F.down.maxAt ⊆ T
  intro k hk
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  exact hF (F.down.sets_subset_support j (F.down.maxAt_mem j))

/-- 概要：空の面族の和上の射影は前合成による同値。
方針：空の面族の和を空の頂点集合の面と同定する。
規約：面族の濃度の帰納法の基底。
使われ方：Kerodon Proposition 4.6.7.23、有限の貼り合わせの開始。 -/
lemma coherentResolutionFaceUnionProjection_empty_isPrecompositionEquivalence (n : ℕ) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u}
      (∅ : Finset (Finset (Fin (n + 1))))) := by
  have hA : coherentResolutionFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      coherentResolutionFace ∅ := by
    rw [coherentResolutionFaceUnion_empty, coherentResolutionFace_empty]
  have hB : stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      stdSimplex.face ∅ := by
    rw [stdSimplexFaceUnion_empty, stdSimplex.face_empty]
  exact (subcomplexRestriction_isPrecompositionEquivalence_congr (coherentResolutionProjection n)
    (coherentResolutionFaceUnion_mapsTo ∅) (coherentResolutionFace_mapsTo ∅) hA hB).mpr
      (coherentResolutionFaceProjection_isPrecompositionEquivalence ∅)

/-- 概要：残りの面の和と交わりでの同値性から一枚加えた和の同値性を得る。
方針：部分複体の和の貼り合わせと、交わりの面族による表示を組み合わせる。
規約：交わりの面族は各頂点集合と T の交わりの image。
使われ方：Kerodon Proposition 4.6.7.23、有限の面の貼り合わせの帰納段階。 -/
lemma coherentResolutionFaceUnionProjection_insert_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) (T : Finset (Fin (n + 1)))
    (eS : IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} S))
    (eI : IsPrecompositionEquivalence
      (coherentResolutionFaceUnionProjection.{u} (S.image (fun U ↦ U ∩ T)))) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} (insert T S)) := by
  let f := coherentResolutionProjection.{u} n
  have hI : coherentResolutionFaceUnion.{u} S ⊓ coherentResolutionFace T ≤
      (stdSimplexFaceUnion S ⊓ stdSimplex.face T).preimage f := by
    intro d F hF
    exact ⟨coherentResolutionFaceUnion_mapsTo S d hF.1, coherentResolutionFace_mapsTo T d hF.2⟩
  have hU : coherentResolutionFaceUnion.{u} S ⊔ coherentResolutionFace T ≤
      (stdSimplexFaceUnion S ⊔ stdSimplex.face T).preimage f := by
    intro d F hF
    rcases hF with hF | hF
    · exact Or.inl (coherentResolutionFaceUnion_mapsTo S d hF)
    · exact Or.inr (coherentResolutionFace_mapsTo T d hF)
  have eIntersection : IsPrecompositionEquivalence (subcomplexRestriction f _ _ hI) :=
    (subcomplexRestriction_isPrecompositionEquivalence_congr f hI
      (coherentResolutionFaceUnion_mapsTo (S.image (fun U ↦ U ∩ T)))
      (coherentResolutionFaceUnion_inf_face S T) (stdSimplexFaceUnion_inf_face S T)).mpr eI
  have eUnion := subcomplexRestriction_isPrecompositionEquivalence_sup f
    (coherentResolutionFaceUnion S) (coherentResolutionFace T)
    (stdSimplexFaceUnion S) (stdSimplex.face T)
    (coherentResolutionFaceUnion_mapsTo S) (coherentResolutionFace_mapsTo T) hI hU
    eIntersection eS (coherentResolutionFaceProjection_isPrecompositionEquivalence T)
  have hA : coherentResolutionFaceUnion.{u} S ⊔ coherentResolutionFace T =
      coherentResolutionFaceUnion (insert T S) :=
    (sup_comm _ _).trans (coherentResolutionFaceUnion_insert T S).symm
  have hB : stdSimplexFaceUnion.{u} S ⊔ stdSimplex.face T = stdSimplexFaceUnion (insert T S) :=
    (sup_comm _ _).trans (stdSimplexFaceUnion_insert T S).symm
  exact (subcomplexRestriction_isPrecompositionEquivalence_congr f hU
    (coherentResolutionFaceUnion_mapsTo (insert T S)) hA hB).mp eUnion

/-- 概要：有限個の面の和上の解像の射影は前合成による同値。
方針：面族の濃度について強い帰納法を使い、交わりの面族も小さくなることを使う。
規約：面の重複、空の面、面族の空性に追加条件を課さない。
使われ方：Kerodon Proposition 4.6.7.23、標準単体の境界上の比較。 -/
lemma coherentResolutionFaceUnionProjection_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) :
    IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} S) := by
  classical
  have go : ∀ k, ∀ R : Finset (Finset (Fin (n + 1))), R.card = k →
      IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} R) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hk
      by_cases hR : R = ∅
      · subst R
        exact coherentResolutionFaceUnionProjection_empty_isPrecompositionEquivalence n
      · obtain ⟨T, hT⟩ := Finset.nonempty_iff_ne_empty.mpr hR
        have hsmall : (R.erase T).card < k := by
          rw [← hk]
          exact Finset.card_erase_lt_of_mem hT
        have hinter : ((R.erase T).image (fun U ↦ U ∩ T)).card < k :=
          lt_of_le_of_lt Finset.card_image_le hsmall
        have eS := ih (R.erase T).card hsmall (R.erase T) rfl
        have eI := ih ((R.erase T).image (fun U ↦ U ∩ T)).card hinter
          ((R.erase T).image (fun U ↦ U ∩ T)) rfl
        have e := coherentResolutionFaceUnionProjection_insert_isPrecompositionEquivalence
          (R.erase T) T eS eI
        exact Eq.mp (congrArg (fun Q : Finset (Finset (Fin (n + 1))) ↦
          IsPrecompositionEquivalence (coherentResolutionFaceUnionProjection.{u} Q))
            (Finset.insert_erase hT)) e
  exact go S.card S rfl

end SerrePositivity.InfinityCategories
