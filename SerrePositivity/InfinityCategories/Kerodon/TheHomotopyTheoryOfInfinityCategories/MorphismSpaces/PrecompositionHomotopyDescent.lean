module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHomotopyTranspose

/-!
# 前合成の同値によるホモトピーの降下と反映

概要：前合成の同値を使い、Kan 標的への射をホモトピーまで降下し、二射のホモトピーを反映する。
方針：関手単体集合の同値の本質的全射性と逆同値の単位の成分を使う。
規約：始域の補助模型には Kan 性を要求しない。
使われ方：HA 1.3.1.17、Kerodon Theorem 4.6.7.5（Tag 01LE） の比較射の逆構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 概要：前合成が同値なら Kan 標的への任意の射はホモトピーまで降下する。
方針：関手単体集合の同値の本質的全射性から像の頂点を選び、同型をホモトピーに戻す。
規約：射の厳密な因子分解や一意性は主張しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE） の解像の余単位からの逆射の選択。 -/
lemma precomposition_exists_homotopy {A B K : SSet.{u}} [KanComplex K]
    (p : A ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence p) (f : A ⟶ K) :
    ∃ g : B ⟶ K, Nonempty (SSet.Homotopy (p ≫ g) f) := by
  obtain ⟨v, ⟨e⟩⟩ := (hp K).choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B K).surjective v
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ g) f := e
  exact ⟨g, ⟨he.simplicialHomotopy⟩⟩

/-- 概要：前合成が同値なら Kan 標的への二射のホモトピーは前合成後から反映できる。
方針：前合成の逆で頂点の同型を戻し、単位の成分で両端を元の二射へ移す。
規約：得られるホモトピーの代表の一意性は要求しない。
使われ方：HA 1.3.1.17 の比較射と逆射の合成の恒等性を解像から戻す。 -/
lemma precomposition_reflect_homotopy {A B K : SSet.{u}} [KanComplex K]
    (p : A ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence p) {f g : B ⟶ K}
    (H : SSet.Homotopy (p ≫ f) (p ≫ g)) : Nonempty (SSet.Homotopy f g) := by
  let q := (hp K).choose
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p ≫ f) (p ≫ g) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H
  have ef := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app q.homInvIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  have eg := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app q.homInvIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
  have em := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e q.inv
  have ei : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := ef.symm ≪≫ em ≪≫ eg
  exact ⟨ei.simplicialHomotopy⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
