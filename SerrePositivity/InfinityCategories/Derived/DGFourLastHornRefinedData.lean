module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinedVertices
public import SerrePositivity.InfinityCategories.DGNerve.SelectedFaceExtensionality

/-! # 細分四次ホーンの回収データと元の全データの閉始点細分の一致

概要：細分ホーンから回収する対象族・全成分は、元の既知データの同じ閉始点細分に等しい。
方針：四つの指定面の一致と、欠面・最上位成分の零を使う。
規約：一部の低次成分だけで済ませない。使われ方：細分後の二残差と供給済み Q・A の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 四次最後ホーンの、指定四面に含まれない成分は全て零。 -/
lemma dgFourLastHornKnownData_zero_unknown
    (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)
    (I : Finset (Fin 5)) (hsub : Finset.univ.erase 4 ⊆ I)
    (a b : Fin 5) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) : (HornData.knownData σ).hom I a b k hI ha hb hk = 0 := by
  have hn : ¬ (I ≠ Finset.univ ∧ I ≠ Finset.univ.erase 4) := by
    intro hh
    obtain ⟨j, hj, hjI⟩ := (HornIndex.exists_covering_face I 4).mpr hh
    exact hjI (hsub (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  dsimp only [HornData.knownData]
  split
  · rename_i hf
    split
    · rename_i hm
      exact (hn ⟨hf, hm⟩).elim
    · rfl
  · rfl

variable (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 細分された四次ホーンの全回収データは、元のデータの同じ閉始点細分そのもの。 -/
lemma dgFourLastHornSourceRefinement_knownData :
    HornData.knownData (dgFourLastHornSourceRefinement σ q s) =
      dgSimplexDataInitialRefinement A D (HornData.knownData σ) q s := by
  let S : Finset (Fin 5) := Finset.univ.erase 4
  have hS : SelectedFaces.CoversVertices S := by
    intro i
    by_cases hi : i = 0
    · exact ⟨1, by decide, by subst i; decide⟩
    · exact ⟨0, by decide, Ne.symm hi⟩
  apply SimplexData.ext_of_selected_faces_zero_unknown S hS
  · intro j hj
    fin_cases j
    · refine (HornData.knownData_pullback_face
        (dgFourLastHornSourceRefinement σ q s) 0 (by decide)).trans ?_
      refine (congrArg (fun t : Simplex A D 3 => t.toSimplexData)
        (dgFourLastHornSourceRefinement_value0 σ q s)).trans ?_
      exact (dgSimplexDataInitialRefinement_pullback_avoids_zero A D
        (HornData.knownData σ) q s (0 : Fin 5).succAboveOrderEmb.toOrderHom
        (0 : Fin 5).succAboveOrderEmb.injective
        (fun i => by change i.succ ≠ 0; exact Fin.succ_ne_zero i)).symm
    · refine (HornData.knownData_pullback_face
        (dgFourLastHornSourceRefinement σ q s) 1 (by decide)).trans ?_
      refine (congrArg (fun t : Simplex A D 3 => t.toSimplexData)
        (dgFourLastHornSourceRefinement_value1 σ q s)).trans ?_
      have hr := (dgSimplexDataInitialRefinement_pullback_fixed_zero A D
        (HornData.knownData σ) q s (1 : Fin 5).succAboveOrderEmb.toOrderHom
        (1 : Fin 5).succAboveOrderEmb.injective rfl).symm
      simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hr
      exact hr
    · refine (HornData.knownData_pullback_face
        (dgFourLastHornSourceRefinement σ q s) 2 (by decide)).trans ?_
      refine (congrArg (fun t : Simplex A D 3 => t.toSimplexData)
        (dgFourLastHornSourceRefinement_value2 σ q s)).trans ?_
      have hr := (dgSimplexDataInitialRefinement_pullback_fixed_zero A D
        (HornData.knownData σ) q s (2 : Fin 5).succAboveOrderEmb.toOrderHom
        (2 : Fin 5).succAboveOrderEmb.injective rfl).symm
      simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hr
      exact hr
    · refine (HornData.knownData_pullback_face
        (dgFourLastHornSourceRefinement σ q s) 3 (by decide)).trans ?_
      refine (congrArg (fun t : Simplex A D 3 => t.toSimplexData)
        (dgFourLastHornSourceRefinement_value3 σ q s)).trans ?_
      have hr := (dgSimplexDataInitialRefinement_pullback_fixed_zero A D
        (HornData.knownData σ) q s (3 : Fin 5).succAboveOrderEmb.toOrderHom
        (3 : Fin 5).succAboveOrderEmb.injective rfl).symm
      simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hr
      exact hr
    · exact ((Finset.notMem_erase (4 : Fin 5) Finset.univ) hj).elim
  · intro I hsub a b k hI ha hb hk
    exact dgFourLastHornKnownData_zero_unknown _ I hsub a b k hI ha hb hk
  · intro I hsub a b k hI ha hb hk
    change dgSourceRefinementHomLinear A D (HornData.knownData σ).obj q s a b k
      ((HornData.knownData σ).hom I a b k hI ha hb hk) = 0
    rw [dgFourLastHornKnownData_zero_unknown σ I hsub a b k hI ha hb hk, map_zero]

end SerrePositivity.InfinityCategories
