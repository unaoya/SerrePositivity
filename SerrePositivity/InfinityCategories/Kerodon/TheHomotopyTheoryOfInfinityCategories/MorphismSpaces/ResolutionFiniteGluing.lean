module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaceUnion

/-!
概要：有限個の面の和上で解像の射影は前合成による同値を与える。
方針：面族の濃度について強い帰納法を使い、一枚の面と残りの和を交わりに沿って貼り合わせる。
規約：全ての面と空の面族を含む。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、境界上の比較の有限帰納法。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：各面は射影で同じ頂点集合の標準単体の面へ写る。
方針：各段の最大元は台に属することを使う。
規約：部分複体の制限条件として述べる。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、制限射の貼り合わせの入力。 -/
lemma coherentResolutionFace_mapsTo {n : ℕ} (T : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace.{u} T ≤ (stdSimplex.face T).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) := by
  intro d F hF
  change Finset.univ.image F.down.maxAt ⊆ T
  intro k hk
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  exact hF (F.down.sets_subset_support j (F.down.maxAt_mem j))

/-- 概要：空の面族の和上の射影は前合成による同値。
方針：空の面族の和を空の頂点集合の面と同定する。
規約：面族の濃度の帰納法の基底。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限の貼り合わせの開始。 -/
lemma coherentResolutionFaceUnionProjection_empty_isPrecompositionEquivalence (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u}
      (∅ : Finset (Finset (Fin (n + 1))))) := by
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace ∅ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_empty, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace_empty]
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} (∅ : Finset (Finset (Fin (n + 1)))) =
      stdSimplex.face ∅ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_empty, stdSimplex.face_empty]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction_isPrecompositionEquivalence_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo ∅) (coherentResolutionFace_mapsTo ∅) hA hB).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_isPrecompositionEquivalence ∅)

/-- 概要：残りの面の和と交わりでの同値性から一枚加えた和の同値性を得る。
方針：部分複体の和の貼り合わせと、交わりの面族による表示を組み合わせる。
規約：交わりの面族は各頂点集合と T の交わりの image。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、有限の面の貼り合わせの帰納段階。 -/
lemma coherentResolutionFaceUnionProjection_insert_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) (T : Finset (Fin (n + 1)))
    (eS : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} S))
    (eI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} (S.image (fun U ↦ U ∩ T)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} (insert T S)) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection.{u} n
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} S ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T ≤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion S ⊓ stdSimplex.face T).preimage f := by
    intro d F hF
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo S d hF.1, coherentResolutionFace_mapsTo T d hF.2⟩
  have hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} S ⊔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T ≤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion S ⊔ stdSimplex.face T).preimage f := by
    intro d F hF
    rcases hF with hF | hF
    · exact Or.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo S d hF)
    · exact Or.inr (coherentResolutionFace_mapsTo T d hF)
  have eIntersection : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction f _ _ hI) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction_isPrecompositionEquivalence_congr f hI
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo (S.image (fun U ↦ U ∩ T)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_inf_face S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_inf_face S T)).mpr eI
  have eUnion := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction_isPrecompositionEquivalence_sup f
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion S) (stdSimplex.face T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo S) (coherentResolutionFace_mapsTo T) hI hU
    eIntersection eS (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_isPrecompositionEquivalence T)
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion.{u} S ⊔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFace T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion (insert T S) :=
    (sup_comm _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_insert T S).symm
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion.{u} S ⊔ stdSimplex.face T = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion (insert T S) :=
    (sup_comm _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexFaceUnion_insert T S).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.subcomplexRestriction_isPrecompositionEquivalence_congr f hU
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnion_mapsTo (insert T S)) hA hB).mp eUnion

/-- 概要：有限個の面の和上の解像の射影は前合成による同値。
方針：面族の濃度について強い帰納法を使い、交わりの面族も小さくなることを使う。
規約：面の重複、空の面、面族の空性に追加条件を課さない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW）、標準単体の境界上の比較。 -/
lemma coherentResolutionFaceUnionProjection_isPrecompositionEquivalence {n : ℕ}
    (S : Finset (Finset (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} S) := by
  classical
  have go : ∀ k, ∀ R : Finset (Finset (Fin (n + 1))), R.card = k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} R) := by
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
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceUnionProjection.{u} Q))
            (Finset.insert_erase hT)) e
  exact go S.card S rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
