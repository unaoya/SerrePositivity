module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyExistence

/-!
概要：大域切断の指定極限錐を、元の全前層圏上の一つの coherent な族として選ぶ。
方針：既存の全極限錐族の存在に各前層の小極限を渡す。
  文献対応：HTT 5.4.7.9、Kerodon §7.1（Tag 02H1）の site 同値に沿う全 Γ 比較。
規約：個々の前層の錐の独立な選択で、全族の射や高次単体を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の全前層圏を厳密に回収する同じ全極限錐族。 -/
def globalSectionsFamilyData
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    {s : PresheafCat C E ⟶ (ihom (join (Δ[0] : SSet.{u + 1}) (presheafShape C))).obj E //
      s ≫ coneRestriction (presheafShape C) E = 𝟙 _ ∧
      ∀ v : (PresheafCat C E) _⦋0⦌, IsLimitCone (functorVertexCone (s.app _ v))} := by
  let h := exists_pointwiseLimitConeFamily (𝟙 (PresheafCat C E))
    (fun v ↦ hasLimit_presheaf hE (vertexToPresheaf v))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- 同じ全族の図式への制限は恒等関手。 -/
lemma globalSectionsFamilyData_restrict
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    (globalSectionsFamilyData (C := C) hE).val ≫ coneRestriction (presheafShape C) E = 𝟙 _ :=
  (globalSectionsFamilyData hE).property.1

/-- 同じ全族の各値は元の極限錐。 -/
lemma globalSectionsFamilyData_isLimit
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (v : (PresheafCat C E) _⦋0⦌) :
    IsLimitCone (functorVertexCone ((globalSectionsFamilyData hE).val.app _ v)) :=
  (globalSectionsFamilyData hE).property.2 v

end SerrePositivity.InfinityCategories.Sheaves
