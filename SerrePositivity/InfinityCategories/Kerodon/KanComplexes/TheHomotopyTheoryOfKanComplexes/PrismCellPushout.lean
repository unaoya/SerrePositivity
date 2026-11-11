module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeJoinPrismHornEquality
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：部分複体に単射のセルを加える正方形の pushout 判定。
方針：交わりを逆像で表し、各次数で単射性と被覆による型の pushout 判定を使う。
規約：通常の単体集合の pushout のみを扱う。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、prism の各段階のホーンの貼り合わせ。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：単射のセルとの交わりが指定した部分複体なら、その追加は pushout。
方針：逆像の等式から pullback を作り、像の和による被覆と単射性を使う。
規約：a と b は部分複体への因子化、ha と hb は全体への合成の式。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、prism のホーンのセルの貼り合わせの判定。 -/
lemma isPushout_prism_mono_cell {X V : SSet.{u}} (A B : X.Subcomplex)
    (P : V.Subcomplex) (σ : V ⟶ X) [Mono σ]
    (hB : A ⊔ Subcomplex.range σ = B) (hP : P = A.preimage σ)
    (a : (P : SSet.{u}) ⟶ A) (b : V ⟶ B)
    (ha : a ≫ A.ι = P.ι ≫ σ) (hb : b ≫ B.ι = σ) :
    IsPushout P.ι a b (Subcomplex.homOfLE (hB ▸ le_sup_left)) := by
  have hp : IsPullback P.ι a σ A.ι := by
    apply IsPullback.of_forall_isPullback_app
    intro n
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨(congrArg (fun f : (P : SSet.{u}) ⟶ X ↦ f.app n) ha).symm, ?_, ?_⟩
    · intro x y h
      exact Subtype.ext h.1
    · intro v x h
      have hv : v ∈ P.obj n := by
        rw [hP]
        change σ.app n v ∈ A.obj n
        exact h ▸ x.property
      refine ⟨⟨v, hv⟩, rfl, ?_⟩
      apply Subtype.ext
      have he := congrArg (fun f : (P : SSet.{u}) ⟶ X ↦ f.app n ⟨v, hv⟩) ha
      exact he.trans h
  apply IsPushout.of_forall_isPushout_app
  intro n
  apply Types.isPushout_of_isPullback_of_mono (hp.app n)
    (k := B.ι.app n)
  · exact congrArg (fun f : V ⟶ X ↦ f.app n) hb
  · rfl
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ A.obj n ∨ x.val ∈ Set.range (σ.app n) := by
      exact (congrArg (fun C : X.Subcomplex ↦ x.val ∈ C.obj n) hB).mpr x.property
    rcases hx with hx | ⟨v, hv⟩
    · exact Or.inr ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · apply Or.inl
      refine ⟨v, Subtype.ext ?_⟩
      exact (congrArg (fun f : V ⟶ X ↦ f.app n v) hb).trans hv
  · intro x y _ _ h
    exact Subtype.ext h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
