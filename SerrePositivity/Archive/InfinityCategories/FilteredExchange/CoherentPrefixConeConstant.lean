module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ConstantOrderDiagram

/-!
概要：定値 cone に対する prefix 変形は同じ定値 cone。
方針：定値豊穣関手の全 Hom が単位を経由することを使う。
規約：任意の tail 単体と時刻で実単体を保持する。
使われ方：零面の実円柱の始点固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 定値 cone の prefix 変形は全単体として同じ定値 cone。 -/
lemma coherentPrefixConeSimplex_constant {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (c : C) {m n : ℕ} (a : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (m + 1) →o Fin 2) :
    coherentPrefixConeSimplex (PinchedHom.constant (coherentNerveVertex c) (n + 1)) a t =
      PinchedHom.constant (coherentNerveVertex c) (m + 1) := by
  rw [coherentNerveVertex_constant, coherentNerveVertex_constant]
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.F2
