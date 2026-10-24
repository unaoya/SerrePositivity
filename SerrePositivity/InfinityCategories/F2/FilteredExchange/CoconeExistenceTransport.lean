module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting
public import SerrePositivity.InfinityCategories.Core.JoinTensor

/-!
概要：同型な coherent 図式の間で余錐の存在を移す。
方針：join の左包含に沿って関手同型を延長し、新しい図式への制限を厳密化する。
規約：余錐の存在のみを扱い、余極限性は要求しない。
使われ方：filtered 性のホモトピー retract・同値による輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：関手として同型な図式が余錐を持てば元の図式も余錐を持つ。
方針：既存の余錐の左端の指定同型を、単射な join の包含に沿って延長する。
規約：有限性や余極限性は不要。使われ方：filtered 性の同値不変性。 -/
lemma nonempty_joinCocone_of_functorIso {K C : SSet.{u}} [Quasicategory C]
    {p q : K ⟶ C} (e : FunctorIso p q) (hp : Nonempty (JoinCocone p)) :
    Nonempty (JoinCocone q) := by
  obtain ⟨c⟩ := hp
  have he : FunctorIso (joinInl K Δ[0] ≫ c.val) q := by rw [c.property]; exact e
  obtain ⟨w, hw⟩ := exists_extension_of_functorIso (joinInl K Δ[0]) c.val q he
  exact ⟨⟨w, hw⟩⟩

end SerrePositivity.InfinityCategories.F2
