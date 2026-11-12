module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashSimplex

/-!
概要：任意個の射影による smash の単体の識別。
方針：非基点の族には非基点の座標があり、その座標から左成分を復元する。
規約：空の添字も含む。空積の smash は一点なので同じ判定が有効。
使われ方：BF 1978 §2、HA §1.4.2。Sp の小積の構造射の単射性。
-/

@[expose] public section
universe u

namespace SerrePositivity.KST.Spectra
noncomputable section

/-- 全座標の smash の像が一致すれば、族との smash の元も一致する。 -/
lemma smashSmallProduct_pack_ext {S A : Type u} {B : S → Type u}
    (a₀ : A) (b₀ : ∀ s, B s) (a a' : A) (b b' : ∀ s, B s)
    (h : ∀ s, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (b₀ s) a (b s) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (b₀ s) a' (b' s)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ b₀ a b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ b₀ a' b' := by
  classical
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff a₀ b₀ a a' b b').mpr
  by_cases ha : a = a₀
  · right
    refine ⟨Or.inl ha, ?_⟩
    by_cases ha' : a' = a₀
    · exact Or.inl ha'
    · right
      funext s
      have hz : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (b₀ s) a' (b' s) = none := by
        rw [← h s]
        exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mpr (Or.inl ha)
      exact ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mp hz).resolve_left ha'
  · by_cases hb : b = b₀
    · right
      refine ⟨Or.inr hb, ?_⟩
      by_cases ha' : a' = a₀
      · exact Or.inl ha'
      · right
        funext s
        have hz : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (b₀ s) a' (b' s) = none := by
          rw [← h s]
          exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mpr (Or.inr (congrFun hb s))
        exact ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_none _ _ _ _).mp hz).resolve_left ha'
    · have hex : ∃ s, b s ≠ b₀ s := by
        by_contra hc
        apply hb
        funext s
        exact Classical.not_not.mp (fun hn ↦ hc ⟨s, hn⟩)
      obtain ⟨s, hs⟩ := hex
      have haa : a = a' := by
        rcases (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff _ _ _ _ _ _).mp (h s) with he | he
        · exact he.1
        · exact False.elim ((he.1.resolve_left ha) |> hs)
      left
      refine ⟨haa, funext fun t ↦ ?_⟩
      rcases (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff _ _ _ _ _ _).mp (h t) with he | he
      · exact he.2
      · have ha' : a' ≠ a₀ := fun he ↦ ha (haa.trans he)
        exact (he.1.resolve_left ha).trans (he.2.resolve_left ha').symm

end
end SerrePositivity.KST.Spectra
