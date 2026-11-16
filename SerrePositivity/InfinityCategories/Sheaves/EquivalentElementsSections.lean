module

public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex

/-!
概要：集合重みの元の圏と同値な通常圏の指定極限を、同じ切断の値と比較する。
方針：元の同値関手の nerve を持ち上げ、底の射影を保持する同値な添字の比較を使う。
規約：元の sectionsOf の選択と与えられた極限錐を保つ。型は drafts/Sheaves/SpaceValued。
使われ方：HTT 5.1.5.6、Kerodon §7.1（Tag 02K2）、S8-6。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の圏と同値な通常圏上の指定極限は、同じ切断の値を与える。
HTT 5.1.5.6、Kerodon §7.1（Tag 02K2）、同値な添字と指定極限の一意性の特殊化。 -/
def sectionsOf_eq_limit_elements (P : Cᵒᵖ ⥤ Type u) (O : Presheaf C E)
    (h : HasLimit (sectionsOfDiagram P O)) {D : Type u} [SmallCategory D]
    (e : D ≌ P.Elements)
    (c : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (e.functor ⋙ Functor.Elements.π P)) ≫ O)) (hc : IsLimitCone c) :
    VertexIso (sectionsOf P O h) c.vertex := by
  have ha : IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap e.functor)) :=
    IsQCatEquivalence.ulift.{u, u + 1} (nerveQCatEquivalence e).isQCatEquivalence
  have hp : (SSet.uliftFunctor.{u + 1, u}).map (nerveMap e.functor) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π P)) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (e.functor ⋙ Functor.Elements.π P)) := by
    rw [← Functor.map_comp]
    rfl
  exact (limitVertexIsoOfOverEquivalence
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap e.functor)) ha hp O c
    (sectionsOfCone P O h) hc (sectionsOfCone_isLimit P O h)).symm

end SerrePositivity.InfinityCategories.Sheaves
