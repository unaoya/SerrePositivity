module

public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyAdjunctionComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyReadback

/-!
概要：全極限錐族の頂点を、大域切断関手と同じ指定 adjunct で比較する。
方針：定値図式の右随伴と全錐の既存の普遍性を組み合わせる。
  文献対応：HTT 5.5.2.9、Kerodon §7.1（Tag 02H1）の Γ の関手性。
規約：全パラメータの一つの関手同型を返し、頂点ごとの同型だけで代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の全極限錐族と Γ の全関手比較。 -/
def globalSectionsConeFamilyIso {A : SSet.{u + 1}} [Quasicategory A]
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (s : A ⟶ (ihom (join (Δ[0] : SSet.{u + 1}) (presheafShape C))).obj E)
    (hs : ∀ x : A _⦋0⦌, IsLimitCone (functorVertexCone (s.app _ x))) :
    FunctorIso (s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (presheafShape C))))
      ((s ≫ coneRestriction (presheafShape C) E) ≫ globalSectionsFunctor hE) :=
  limitConeFamily_apexIso_of_constantAdjunction (globalSectionsAdjunction hE) s hs

/-- 指定した一つの極限錐は Γ の同じ右随伴の値と同型。 -/
def globalSectionsConeValueIso
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {F : Presheaf C E} (c : JoinCone F) (hc : IsLimitCone c) :
    VertexIso c.vertex ((globalSectionsFunctor hE).app _ (functorVertex F)) := by
  let s : (Δ[0] : SSet.{u + 1}) ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) (presheafShape C))).obj E :=
    SSet.const (functorVertex c.val)
  have hs : ∀ x : (Δ[0] : SSet.{u + 1}) _⦋0⦌,
      IsLimitCone (functorVertexCone (s.app _ x)) := by
    intro x
    have hv : s.app _ x = functorVertex c.val := by
      change ((ihom _).obj E).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op _ = _
      have hi : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
      rw [hi, op_id, CategoryTheory.Functor.map_id_apply]
    rw [hv]
    exact (isLimitCone_functorVertexCone_functorVertex c).mpr hc
  let e := (globalSectionsConeFamilyIso hE s hs).toNatIso.app
    (SSet.HomotopyCategory.mk (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}))))
  have hv : s.app _ (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1}))) =
      functorVertex c.val := by
    change ((ihom _).obj E).map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op _ = _
    have hi : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
    rw [hi, op_id, CategoryTheory.Functor.map_id_apply]
  change VertexIso
    ((evaluateFunctorAt (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) (presheafShape C)))).app _
      (s.app _ (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))))
    ((globalSectionsFunctor hE).app _ ((coneRestriction (presheafShape C) E).app _
      (s.app _ (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))))) at e
  rw [hv, evaluateFunctorAt_functorVertex] at e
  have hr : (coneRestriction (presheafShape C) E).app _ (functorVertex c.val) =
      functorVertex F := by
    change functorVertex (joinInr _ _ ≫ c.val) = functorVertex F
    rw [c.property]
  rw [hr] at e
  exact e

end SerrePositivity.InfinityCategories.Sheaves
