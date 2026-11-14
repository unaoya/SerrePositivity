module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.SimplicialSum
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedCoproducts

/-!
# 添字付き余積と局所化同型

概要：成分ごとの局所化同型は、次数ごとの依存和の射も局所化同型にする。
方針：証明済みの抽象的な余積保存を、余積の普遍性から得る同型で移す。
規約：Segal 1974 Lemma 1.8 の telescope の模型の不変性。
使われ方：成分ごとのファイバー比較を余積へまとめる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel
variable {ι : Type v}

/--
概要：添字付き余積の成分ごとの局所化同型の射は局所化同型である。
方針：具体的な依存和と抽象的な余積の同型の自然性で可逆性を移す。
規約：対象の Kan 性や射の単射性は不要。
使われ方：telescope の各段階の模型の比較。
-/
theorem simplicialSumMap_localized_isIso {A B : ι → SSet.{max u v}}
    (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (f i))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f)) := by
  let eA := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct A).coconePointUniqueUpToIso (coproductIsCoproduct A)
  let eB := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct B).coconePointUniqueUpToIso (coproductIsCoproduct B)
  have heA i : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ eA.hom = Sigma.ι A i :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct A).comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct A) ⟨i⟩
  have heB i : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B i ≫ eB.hom = Sigma.ι B i :=
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumIsCoproduct B).comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct B) ⟨i⟩
  have he : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f ≫ eB.hom = eA.hom ≫ Limits.Sigma.map f := by
    apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
    intro i
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map, Category.assoc, heB,
      ← Category.assoc, heA, Sigma.ι_map]
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have := KanLocalizedCoproducts.localized_isIso ι f hf
  have h : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f) ≫ Q.map eB.hom) := by
    rw [← Q.map_comp, he, Q.map_comp]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end SerrePositivity.KST.Comparison
