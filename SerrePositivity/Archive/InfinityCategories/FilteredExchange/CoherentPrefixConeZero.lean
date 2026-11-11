module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentPrefixConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexDeformation

/-!
概要：固定始点の prefix 円柱の時刻零は元の cone の最大 path 表示。
方針：prefix の全区間と既存の suffix の全区間を同じ path で同定する。
規約：元の豊穣図式と全次数の制限を保持する。
使われ方：零面の指定比較円柱の最大化側の端点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全区間を埋める二つの変形は同じ実 path。 -/
lemma coherentPrefixPathDeformation_zero_eq_suffix
    {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) {i j : J} (P : Path i j) :
    coherentPrefixPathDeformation A (OrderHom.const J 0) P =
      coherentPathDeformation A (OrderHom.const J 1) P := by
  apply SimplicialThickening.Path.ext
  rw [coherentPrefixPathDeformation_zero, coherentPathDeformation_one]

/-- 時刻零の prefix 豊穣関手は既存の最大化豊穣関手。 -/
lemma coherentPrefixPathDeformationEnriched_zero
    {J K : Type u} [LinearOrder J] [LinearOrder K] (A : J →o K) :
    coherentPrefixPathDeformationEnriched A (OrderHom.const J 0) =
      coherentPathDeformationEnriched A (OrderHom.const J 1) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ coherentPrefixPathDeformation_zero_eq_suffix A (P.obj z))

/-- 時刻零の固定始点の prefix 単体は元の cone の最大化の実際の制限。 -/
lemma coherentPrefixConeSimplex_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n + 1⦌)
    (a : Fin (m + 1) →o Fin (n + 1)) :
    coherentPrefixConeSimplex s a (OrderHom.const _ 0) =
      (SimplicialThickening.functor (prependOrderHom a).uliftMap).comp SSet
        (coherentSimplexMaximalization s) := by
  unfold coherentPrefixConeSimplex
  have ht : (coherentPrefixConeTime (OrderHom.const _ 0)).comp
      (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin (m + 2)) →o _) =
        OrderHom.const _ 0 := by
    ext k
    rcases k with ⟨k⟩
    induction k using Fin.cases with
    | zero => rfl
    | succ k => rfl
  rw [ht, coherentPrefixPathDeformationEnriched_zero]
  exact congrArg (fun F ↦ F.comp SSet s)
    (coherentPathDeformationEnriched_reindex (prependOrderHom a).uliftMap
      (OrderHom.id (α := ULift.{u} (Fin (n + 2)))) (OrderHom.const _ 1)).symm

end SerrePositivity.InfinityCategories.F2
