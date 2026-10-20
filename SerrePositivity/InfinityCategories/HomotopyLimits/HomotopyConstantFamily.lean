module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianIntervalPostcomposition
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.FunctorHomEvaluationNaturality

/-!
概要：指定ホモトピーの各点の評価を、任意の定値パラメータ族で表す。
方針：元の円柱を定値写像で引き戻し、h Fun の評価の端点を揃える。
規約：ホモトピー代表を選び直さない。使われ方：輸送の自然性の区間族での表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A X Y : SSet.{u}} {U V : X ⟶ Y}
  (H : SSet.Homotopy U V) {x y : X _⦋0⦌}
  (f : A ⟶ intervalMappingSpace x y)
/-- 指定ホモトピーの頂点での制限を、定値族間のホモトピーで表す。 -/
def homotopyConstantFamily (z : X _⦋0⦌) : SSet.Homotopy
    (SSet.const (U.app (Opposite.op ⦋0⦌) z) : A ⟶ Y)
    (SSet.const (V.app (Opposite.op ⦋0⦌) z)) where
  h := ((SSet.const z : A ⟶ X) ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀, SSet.const_comp]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, SSet.const_comp]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 指定ホモトピーの評価の定値族は、元の円柱の定値族の Hom 類である。 -/
lemma homotopyConstantFamily_hom (z : X _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (homotopyConstantFamily (A := A) H z)) =
    constantFunctorHomMap A (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) z) := by
  rw [← functorHomEvaluate_constantFunctorHomMap]
  rw [← functorHomotopyPrecomp_hom]
  symm
  exact homMk_transport (congrArg functorVertex (SSet.const_comp z U))
    (congrArg functorVertex (SSet.const_comp z V))
    (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H (SSet.const z : A ⟶ X)))
    (functorEdgeOfSimplicialHomotopy (homotopyConstantFamily (A := A) H z)) rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
