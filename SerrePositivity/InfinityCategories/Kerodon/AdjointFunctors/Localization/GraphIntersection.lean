module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityPreimageRecovery
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 元の全語の graph の包含の像の交わり

概要：列の像の交わりから得た部分語の graph の像は、二つの元の graph の像の交わり。
方針：全単体の像を恒等列の条件に移し、列の集合の交わりを使う。
規約：元の全行と全作用素を保持した部分複体の等式。
使われ方：Dwyer–Kan §4.4・5.4 の元の graph 図式の proper 性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c) {X Y : C}

lemma identityOutside_intersection (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W c X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) R ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside g R := by
  classical
  have hn (j : Fin c.length) :
      (∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g).orderHom k ≠ j) ↔
        (∀ i, f.orderHom i ≠ j) ∨ (∀ i, g.orderHom i ≠ j) := by
    have hmem := congrArg (fun S : Set (Fin c.length) => j ∈ S)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range f g)
    simp only [Set.mem_inter_iff, Set.mem_range] at hmem
    simpa only [not_exists, not_and_or] using not_congr (iff_of_eq hmem)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside
  simp only [hn, or_imp, forall_and]

/-- 同じ元の部分複体として、列の交わりの像は graph の像の交わりに一致。 -/
lemma graphDiagram_intersection_range [W.IsMultiplicative]
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom) :
    Subfunctor.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)) =
      Subfunctor.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f) ⊓
        Subfunctor.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g) := by
  ext n τ
  change τ ∈ Set.range (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)).app n) ↔
    τ ∈ Set.range (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n) ∧
      τ ∈ Set.range (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g).app n)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_injective f g),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside f hf,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside g hg, ← forall_and]
  exact forall_congr' (fun j => identityOutside_intersection f g (τ.obj j))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
