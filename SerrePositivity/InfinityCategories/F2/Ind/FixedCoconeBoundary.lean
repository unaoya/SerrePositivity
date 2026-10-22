module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeUncurry

/-!
概要：底図式と指定終点を共に固定する、全余錐の関手空間の実 fiber。
方針：二つの厳密制限を内部 Hom の積に束ね、その同じ頂点上の fiber を取る。
規約：fiber の quasicategory 性を仮定しない。使われ方：固定条件を保つ相対同型の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 全余錐から、その元の底図式と頂点図式への厳密な制限の対。 -/
def coconeBoundaryPairRestriction (A X : SSet.{u}) :
    (ihom (join A (Δ[0] : SSet.{u}))).obj X ⟶
      (ihom A).obj X ⊗ (ihom (Δ[0] : SSet.{u})).obj X :=
  lift ((pre (joinInl A Δ[0])).app X) ((pre (joinInr A Δ[0])).app X)

/-- 元の底と終点を共に固定した全余錐の実 fiber。 -/
def fixedCoconeBoundary {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) :
    SSet.{u} := vertexFiber (coconeBoundaryPairRestriction A X) (functorVertex b, functorVertex p)

/-- 指定全余錐を、同じ二つの固定境界の fiber の頂点として表す。 -/
def fixedCoconeBoundaryVertex {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
    (c : join A (Δ[0] : SSet.{u}) ⟶ X) (hl : joinInl A Δ[0] ≫ c = b)
    (hr : joinInr A Δ[0] ≫ c = p) : (fixedCoconeBoundary p b) _⦋0⦌ :=
  ⟨functorVertex c, by
    change (functorVertex (joinInl A Δ[0] ≫ c), functorVertex (joinInr A Δ[0] ≫ c)) =
      PinchedHom.constant (X := (ihom A).obj X ⊗ (ihom (Δ[0] : SSet.{u})).obj X)
        (functorVertex b, functorVertex p) 0
    rw [hl, hr, pinchedConstant_zero]⟩

end SerrePositivity.InfinityCategories.F2.Ind
