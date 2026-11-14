module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveDataRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorNoninjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorThreeSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCandidateTwoSimplex
/-!
概要：全次元 tensor 候補の全データは、面・退化を含む全ての単調写像に自然である。
方針：源の次数で強帰納し、単射の場合・非単射な全体成分・真の部分集合への制限を照合する。
規約：生のデータの全自然性。四次元以上の HA は別途必要。使われ方：実 tensor 関手の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 全次元の同じ tensor 候補データは、全ての単調写像に沿う制限と厳密に可換。 -/
lemma dgNerveTensorDataCandidate_naturality {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α) := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hα : Function.Injective α
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_pullback R B C s t α hα
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
        (s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α)
        (t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)) rfl
      apply heq_of_eq
      funext I a b k hI ha hb hk
      by_cases hIu : I = Finset.univ
      · subst I
        have hi : ¬ Set.InjOn α ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
          intro hi
          apply hα
          intro x y hxy
          exact hi (by simp) (by simp) hxy
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_noninjective_agreement R B C s t α
          Finset.univ a b k hI ha hb hk hi
      · have hproper : I.card < m + 1 := by
          have hle := Finset.card_le_univ I
          simp only [Fintype.card_fin] at hle
          have hne : I.card ≠ m + 1 := by
            intro hc
            apply hIu
            exact Finset.eq_of_subset_of_card_le (Finset.subset_univ I) (by simp [hc])
          omega
        have hres : ∀ (r : ℕ), r < m → ∀ (γ : Fin (r + 1) →o Fin (m + 1)),
            Function.Injective γ →
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).pullback γ =
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).pullback γ := by
          intro r hr γ hγ
          calc
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).pullback γ =
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback (α.comp γ) :=
              _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp _ γ α
            _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback (α.comp γ))
                (t.pullback (α.comp γ)) := ih r hr (n := n) s t (α.comp γ)
            _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C ((s.pullback α).pullback γ)
                ((t.pullback α).pullback γ) := by
              rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp]
            _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).pullback γ :=
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_pullback R B C (s.pullback α) (t.pullback α) γ hγ).symm
        exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveData_hom_heq_of_smaller_restrictions R (DGTensorCategory R B C)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α))
          hres I a b k hI ha hb hk hproper)
/-- 実三単体への全ての退化は、元の同じ二単体の tensor の退化に厳密に一致する。 -/
lemma dgTensorThreeSimplex_sigma (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorThreeSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).σ i s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).σ i t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGTensorCategory R B C)).σ i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C
      (s.toSimplexData.pullback (SimplexCategory.σ i).toOrderHom)
      (t.toSimplexData.pullback (SimplexCategory.σ i).toOrderHom) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C s t).toSimplexData.pullback (SimplexCategory.σ i).toOrderHom
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_two R B C s t]
  exact (dgNerveTensorDataCandidate_naturality R B C s.toSimplexData t.toSimplexData
    (SimplexCategory.σ i).toOrderHom).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
