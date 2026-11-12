module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：fat join の頂点は左右の因子のいずれかに由来する。
方針：二段の pushout の各次数での全射性と区間の二頂点を使う。
規約：左右の因子の非空性は要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の頂点上の可逆性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の各頂点は左包含または右包含の像。
方針：pushout の二つの全射性を使い、円柱の頂点では区間の零か一で分ける。
規約：因子の quasicategory 性も非空性も不要。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの頂点の固定。 -/
lemma fatJoin_vertex_cases (A B : SSet.{u}) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B) _⦋0⦌) :
    (∃ a : A _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B).app (Opposite.op ⦋0⦌) a = x) ∨
      ∃ b : B _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B).app (Opposite.op ⦋0⦌) b = x := by
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌)
  have h₂ := (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd A B) (snd A B)).map ev
  obtain ⟨z, rfl⟩ | ⟨b, rfl⟩ := Types.eq_or_eq_of_isPushout h₂ x
  · have h₁ := (IsPushout.of_hasPushout (SSet.ι₀ (X := A) ▷ B) (fst A B)).map ev
    obtain ⟨⟨⟨a, t⟩, b⟩, rfl⟩ | ⟨a, rfl⟩ := Types.eq_or_eq_of_isPushout h₁ z
    · obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
      fin_cases i
      · left
        refine ⟨a, ?_⟩
        exact (congrArg (fun f : A ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ↦
          f.app (Opposite.op ⦋0⦌) (a, b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero A B)).symm
      · right
        refine ⟨b, ?_⟩
        exact (congrArg (fun f : A ⊗ B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ↦
          f.app (Opposite.op ⦋0⦌) (a, b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one A B)).symm
    · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨b, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
