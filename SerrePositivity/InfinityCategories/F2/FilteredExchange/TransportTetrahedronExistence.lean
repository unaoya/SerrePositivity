module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronDiagram
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplexInitialLift

/-!
概要：元の初期値を固定した実四面体図式は、任意の底の四面体族に存在する。
方針：同じ実全単体を持ち上げ、四頂点の実値を fiber へ戻す。
規約：四面の整合性を入力しない。使われ方：元の三射の高次族への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の実底四面体族は、同じ初期値を保持する一つの実四面体図式を持つ。 -/
lemma exists_transportTetrahedronDiagram {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (β : (Δ[3] : SSet.{u}) ⊗ P ⟶ B)
    (v : Fin 4 → B _⦋0⦌) (hv : ∀ i, simplexPrismVertex 3 i P ≫ β = SSet.const (v i))
    (q : P ⟶ vertexFiber p (v 0)) :
    ∃ (f : ∀ i, P ⟶ vertexFiber p (v i)) (D : TransportTetrahedronDiagram p v f),
      f 0 = q ∧ D.simplex ≫ p = β := by
  obtain ⟨W, hWp, hW₀⟩ := exists_simplexInitialLift p 3 β (q ≫ vertexFiberι p (v 0))
    (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, hv])
  have hvertex (i : Fin 4) : (simplexPrismVertex 3 i P ≫ W) ≫ p = SSet.const (v i) := by
    rw [Category.assoc, hWp, hv]
  let f (i : Fin 4) := vertexFiberLift p (v i) (simplexPrismVertex 3 i P ≫ W) (hvertex i)
  let D : TransportTetrahedronDiagram p v f := ⟨W, fun _ => rfl⟩
  refine ⟨f, D, ?_, hWp⟩
  apply vertexFiber_hom_ext p (v 0)
  exact hW₀

end SerrePositivity.InfinityCategories.F2
