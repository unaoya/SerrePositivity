module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIntersection
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityPreimageRecovery
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 元の全語の graph の包含の像の交わり

概要：列の像の交わりから得た部分語の graph の像は、二つの元の graph の像の交わり。
方針：全単体の像を恒等列の条件に移し、列の集合の交わりを使う。
規約：元の全行と全作用素を保持した部分複体の等式。
使われ方：Dwyer–Kan §4.4・5.4 の元の graph 図式の proper 性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b c : Word} (f : a ⟶ c) (g : b ⟶ c) {X Y : C}

lemma identityOutside_intersection (R : Zigzag W c X Y) :
    IdentityOutside (Word.intersectionInclusion f g) R ↔
      IdentityOutside f R ∧ IdentityOutside g R := by
  classical
  have hn (j : Fin c.length) :
      (∀ k, (Word.intersectionInclusion f g).orderHom k ≠ j) ↔
        (∀ i, f.orderHom i ≠ j) ∨ (∀ i, g.orderHom i ≠ j) := by
    have hmem := congrArg (fun S : Set (Fin c.length) => j ∈ S)
      (Word.intersectionInclusion_range f g)
    simp only [Set.mem_inter_iff, Set.mem_range] at hmem
    simpa only [not_exists, not_and_or] using not_congr (iff_of_eq hmem)
  unfold IdentityOutside
  simp only [hn, or_imp, forall_and]

/-- 同じ元の部分複体として、列の交わりの像は graph の像の交わりに一致。 -/
lemma graphDiagram_intersection_range [W.IsMultiplicative]
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom) :
    Subfunctor.range ((graphDiagram W X Y).map (Word.intersectionInclusion f g)) =
      Subfunctor.range ((graphDiagram W X Y).map f) ⊓
        Subfunctor.range ((graphDiagram W X Y).map g) := by
  ext n τ
  change τ ∈ Set.range (((graphDiagram W X Y).map (Word.intersectionInclusion f g)).app n) ↔
    τ ∈ Set.range (((graphDiagram W X Y).map f).app n) ∧
      τ ∈ Set.range (((graphDiagram W X Y).map g).app n)
  rw [graphDiagram_map_range_iff_identityOutside _ (Word.intersectionInclusion_injective f g),
    graphDiagram_map_range_iff_identityOutside f hf,
    graphDiagram_map_range_iff_identityOutside g hg, ← forall_and]
  exact forall_congr' (fun j => identityOutside_intersection f g (τ.obj j))

end SerrePositivity.EInfinity.Hammock
