module

public import SerrePositivity.InfinityCategories.F2.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：全錐を表す関手頂点の同型は、元の図式が異なっても極限性を保つ。
方針：頂点表示の往復で元の全錐の関手同型へ戻し、既存の移送を使う。
規約：元の全錐を保持。使われ方：指定余極限余錐への完成後の極限性の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全錐を表す頂点の同型を、元の全錐の関手同型へ読み戻す。 -/
def functorVertexConeIso {K X : SSet.{u}} [Quasicategory X]
    {v w : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌} (e : VertexIso v w) :
    FunctorIso (functorVertexCone v).val (functorVertexCone w).val := by
  have hv : functorVertex (functorVertexCone v).val = v :=
    (functorVertexEquiv _ _).apply_symm_apply v
  have hw : functorVertex (functorVertexCone w).val = w :=
    (functorVertexEquiv _ _).apply_symm_apply w
  change VertexIso (functorVertex (functorVertexCone v).val)
    (functorVertex (functorVertexCone w).val)
  rw [hv, hw]
  exact e

/-- 全錐の関手頂点が同型なら、元の完成後の極限性は同値。 -/
lemma isLimitCone_functorVertexCone_iff_of_vertexIso {K X : SSet.{u}} [Quasicategory X]
    {v w : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌} (e : VertexIso v w) :
    IsLimitCone (functorVertexCone v) ↔ IsLimitCone (functorVertexCone w) :=
  ⟨fun h => h.of_functorIso (functorVertexConeIso e),
    fun h => h.of_functorIso (functorVertexConeIso e.symm)⟩

end SerrePositivity.InfinityCategories.F2
