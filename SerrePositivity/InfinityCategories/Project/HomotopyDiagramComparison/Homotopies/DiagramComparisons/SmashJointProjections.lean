module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SmashProductMono

/-!
概要：smash の右因子を識別する射影族は smash の単体も識別する。
方針：非基点の組の具体的表示で、右成分の全像から元の成分を復元する。
規約：射影は基点を保ち、単射性は族全体に要求する。
使われ方：BF 1978 §2、HTT 4.2.4.1、Sp の塔の極限の構造射の単射性。
-/

@[expose] public section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：右因子を識別する基点保存写像の族は smash の組の標準像も識別する。
方針：標準像の等式の核を使い、基点へ潰れる場合と非基点の組を分ける。
規約：空の射影族でも、元の族が単射であれば成立する。
使われ方：塔の射影を使う smash の単体の識別の集合論的部分。 -/
lemma smashSimplexPack_eq_of_family {A B : Type u} {J : Type v} {C : J → Type u}
    (a₀ : A) (b₀ : B) (c₀ : ∀ i, C i) (f : ∀ i, B → C i)
    (hf : ∀ i, f i b₀ = c₀ i) (hinj : Function.Injective (fun b ↦ fun i ↦ f i b))
    (a a' : A) (b b' : B)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (c₀ i) a (f i b) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ (c₀ i) a' (f i b')) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ b₀ a b = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack a₀ b₀ a' b' := by
  classical
  have hh (i : J) := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff a₀ (c₀ i) a a' (f i b) (f i b')).mp (h i)
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack_eq_iff a₀ b₀ a a' b b').mpr
  by_cases ha : a = a₀
  · right
    refine ⟨Or.inl ha, ?_⟩
    by_cases ha' : a' = a₀
    · exact Or.inl ha'
    · right
      apply hinj
      funext i
      rcases hh i with h | h
      · exact False.elim (ha' (h.1.symm.trans ha))
      · exact (h.2.resolve_left ha').trans (hf i).symm
  by_cases ha' : a' = a₀
  · right
    refine ⟨Or.inr ?_, Or.inl ha'⟩
    apply hinj
    funext i
    rcases hh i with h | h
    · exact False.elim (ha (h.1.trans ha'))
    · exact (h.1.resolve_left ha).trans (hf i).symm
  have hbb : b = b' := by
    apply hinj
    funext i
    rcases hh i with h | h
    · exact h.2
    · exact (h.1.resolve_left ha).trans (h.2.resolve_left ha').symm
  subst b'
  by_cases hb : b = b₀
  · exact Or.inr ⟨Or.inr hb, Or.inr hb⟩
  have hi : ∃ i, f i b ≠ c₀ i := by
    by_contra hn
    push Not at hn
    apply hb
    apply hinj
    funext i
    exact (hn i).trans (hf i).symm
  obtain ⟨i, hi⟩ := hi
  rcases hh i with h | h
  · exact Or.inl ⟨h.1, rfl⟩
  · exact False.elim (hi (h.1.resolve_left ha))

/-- 概要：右因子の各次数を識別する点つき射の族は smash の各次数を識別する。
方針：組の代表を取り、具体的 smash 表示で射影族の核の計算を使う。
規約：左因子の Kan 性と右因子の Kan 性は不要。
使われ方：塔の極限の懸垂構造射の単射性の検証。 -/
lemma smashMap_jointlyInjective {J : Type v} (A B : PointedSimplicialSet.{u})
    (C : J → PointedSimplicialSet.{u}) (f : ∀ i, B ⟶ C i) (m : SimplexCategoryᵒᵖ)
    (hf : Function.Injective (fun b ↦ fun i ↦ (f i).right.app m b))
    (s t : (PointedObject.smash A B).right.obj m)
    (h : ∀ i, (PointedObject.smashMap (𝟙 A) (f i)).right.app m s =
      (PointedObject.smashMap (𝟙 A) (f i)).right.app m t) : s = t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A B m s
  obtain ⟨⟨a', b'⟩, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashQuotient_app_surjective A B m t
  have he := smashSimplexPack_eq_of_family (PointedSimplicialSet.basepointAt A m)
    (PointedSimplicialSet.basepointAt B m) (fun i ↦ PointedSimplicialSet.basepointAt (C i) m)
    (fun i ↦ (f i).right.app m) (fun i ↦ PointedSimplicialSet.hom_basepointAt (f i) m)
    hf a a' b b' (fun i ↦ by
      have hi := h i
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashMap_quotient_app] at hi
      have hi' := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel A (C i)).right.app m z) hi
      rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashToSimplexModel_quotient_app] at hi'
      change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A m)
        (PointedSimplicialSet.basepointAt (C i) m) a ((f i).right.app m b) =
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.smashSimplexPack (PointedSimplicialSet.basepointAt A m)
            (PointedSimplicialSet.basepointAt (C i) m) a' ((f i).right.app m b') at hi'
      exact hi')
  have he' := congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp A B m) he
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A B m a b).symm.trans
    (he'.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.simplexModelToSmashApp_pack A B m a' b'))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
