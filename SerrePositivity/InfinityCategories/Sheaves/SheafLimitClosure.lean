module

public import SerrePositivity.InfinityCategories.Sheaves.Sheafification
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjectLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.EquivalenceSmallLimits

/-!
概要：層の頂点条件の極限閉性と、極限を保つ係数移送を固定する。
方針：生成辺の局所性により既存の極限閉性を適用し、係数移送には元の篩錐を使う。
使われ方：HTT 6.2.2.7、Kerodon Tag 06VHの局所対象の極限閉性。
規約：極限錐は元の前層圏の錐。新たな極限の存在を前提に加えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]
variable {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]

/-- 元の全前層圏で取った、層の coherent 図式の極限頂点は層。 -/
theorem sheafProperty_limitCone (J : GrothendieckTopology C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    {K : SSet.{u + 1}} {D : K ⟶ PresheafCat C E}
    (c : JoinCone D) (hc : IsLimitCone c)
    (hD : ∀ k : K _⦋0⦌, sheafProperty J (D.app _ k)) : sheafProperty J c.vertex := by
  obtain ⟨I, edges, hW⟩ := exists_sheafGeneratingEdges J hE
  exact (hW c.vertex).mp (isLocalObject_limitCone (Set.range edges) c hc
    (fun k ↦ (hW _).mpr (hD k)))

/-- 範囲内の小極限を保つ係数関手は、同じ篩錐による層条件を保つ。 -/
lemma IsSheaf.postcomp_of_preservesSmallLimits {J : GrothendieckTopology C}
    {F : Presheaf C E} (hF : IsSheaf J F) (G : E ⟶ B)
    (hG : PreservesSmallLimits G) : IsSheaf J (F ≫ G) := by
  intro U S hS
  exact hG (nerve (sieveCategory S)ᵒᵖ) (restriction F S) (restrictionCone F S) (hF U S hS)

/-- 係数の同値は全ての元の篩極限錐を保つので、層条件を保つ。 -/
lemma IsSheaf.postcomp_of_equivalence {J : GrothendieckTopology C}
    {F : Presheaf C E} (hF : IsSheaf J F) (e : QCatEquivalence E B) :
    IsSheaf J (F ≫ e.hom) := by
  intro U S hS
  exact (e.isLimitCone_iff (restrictionCone F S)).mp (hF U S hS)

end SerrePositivity.InfinityCategories.Sheaves
