module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorConstFiber

/-!
概要：同じ定値の底上の相対同型を、指定 fiber への関手同型へ移す。
方針：定値相対関手から fiber 内部 Hom への既存の写像を使う。
規約：fiber への二つの実際の射を保持。使われ方：密度評価の値写像の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ定値底上の同型は、指定 fiber 内の元の二射の関手同型になる。 -/
def relativeConstantValueIso {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f g : A ⟶ vertexFiber p b)
    (e : VertexIso
      (relativeFunctorVertex p (SSet.const b) (f ≫ vertexFiberι p b)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]))
      (relativeFunctorVertex p (SSet.const b) (g ≫ vertexFiberι p b)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]))) : FunctorIso f g := by
  have h := e.map (relativeFunctorConstFiberHom (A := A) p b)
  rw [relativeFunctorConstFiberHom_vertex, relativeFunctorConstFiberHom_vertex] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
