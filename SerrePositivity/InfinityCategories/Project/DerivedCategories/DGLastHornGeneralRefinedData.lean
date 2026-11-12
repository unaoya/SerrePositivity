module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralSourceRefinement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceExtensionality

/-! # 一般細分ホーンの回収データと同じ全体細分の一致

概要：新ホーンの全対象・全成分を、元の既知全体データの同じ閉始点細分へ同定する。
方針：全指定面の一致と、残る未知二集合の零を使う。
規約：低次の一部の成分だけの比較で済ませない。使われ方：残差と原始元の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}

/-- 実最後ホーンの指定面に含まれない全成分は零。 -/
lemma dgGeneralLastHornKnownData_zero_unknown
    (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (hsub : Finset.univ.erase (Fin.last (n + 2)) ⊆ I)
    (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ (I ≠ Finset.univ ∧ I ≠ Finset.univ.erase (Fin.last (n + 2))) := by
    intro hh
    obtain ⟨j, hj, hjI⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face I (Fin.last (n + 2))).mpr hh
    exact hjI (hsub (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData]
  split
  · rename_i hf
    split
    · rename_i hm
      exact (hn ⟨hf, hm⟩).elim
    · rfl
  · rfl

variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 全次元の新ホーンから回収する全体データは、元の同じ全体細分に等しい。 -/
lemma dgGeneralLastHornSourceRefinement_knownData :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement σ q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s := by
  let S : Finset (Fin (n + 3)) := Finset.univ.erase (Fin.last (n + 2))
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices S := by
    intro i
    by_cases hi : i = 0
    · refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n,
        Finset.mem_erase.mpr ⟨ne_of_lt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n), Finset.mem_univ _⟩, ?_⟩
      rw [hi]
      exact ne_of_gt (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n)
    · exact ⟨0, Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩, Ne.symm hi⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ext_of_selected_faces_zero_unknown S hS
  · intro j hj
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement_knownData_face σ q s j (Finset.mem_erase.mp hj).1
  · intro I hsub a b k hI ha hb hk
    exact dgGeneralLastHornKnownData_zero_unknown _ I hsub a b k hI ha hb hk
  · intro I hsub a b k hI ha hb hk
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj q s a b k
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).hom I a b k hI ha hb hk) = 0
    rw [dgGeneralLastHornKnownData_zero_unknown σ I hsub a b k hI ha hb hk, map_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
