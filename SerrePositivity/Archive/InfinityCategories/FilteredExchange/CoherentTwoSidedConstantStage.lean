module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomSimplex

/-!
概要：元の定値 Hom 係数では、二側 Hom 補間は補間段階に依存しない。
方針：同じ二対象を固定し、交差 Hom の定値係数だけを計算する。
規約：全次数と全区間ラベルを保持。使われ方：固定射での二側比較の類の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ定値 Hom 係数における二側 coherent 単体は、任意の補間段階で一致する。 -/
lemma coherentTwoSidedHomSimplex_constant_stage {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (x : (SimplicialCategory.sHom X Y) _⦋0⦌)
    {n : ℕ} (t s r : Fin (n + 1) →o Fin 2) :
    coherentTwoSidedHomSimplex (SSet.const x) t s =
      coherentTwoSidedHomSimplex (SSet.const x) t r := by
  apply EnrichedFunctor.ext SSet (fun _ => rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change coherentTwoSidedHom (SSet.const x) t s i j =
    coherentTwoSidedHom (SSet.const x) t r i j
  unfold coherentTwoSidedHom
  split_ifs <;> simp only [pathCutEdgewiseStageMap, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
