module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareTopMiddleHomotopy
public import SerrePositivity.InfinityCategories.Stable.FixedMapHomotopyEvaluation
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-! # 零角変更の実四角形ホモトピーの可逆性

概要：左上の中間対象の両端が零頂点なら、変更ホモトピーは全四角形の関手同型。
方針：下側三頂点では定値性、残る頂点では終対象間の射の可逆性を使う。
規約：指定された実ホモトピーを同型の順方向に使う。使われ方：F(0) への零角変更。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial

private lemma fixed_map_vertex_invertible {B K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (H : SSet.Homotopy F G) (i : B ⟶ K)
    (hi : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst B Δ[1] ≫ i ≫ F) (b : B _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) b)).toTruncated := by
  have he := congrArg (fun q : B ⊗ (Δ[1] : SSet.{u}) ⟶ X =>
    q.app (Opposite.op ⦋1⦌) (PinchedHom.constant b 1, homotopyIntervalEdge.edge)) hi
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (PinchedHom.constant b 1), homotopyIntervalEdge.edge) =
      F.app (Opposite.op ⦋1⦌) (i.app (Opposite.op ⦋1⦌) (PinchedHom.constant b 1)) at he
  rw [pinchedConstant_map, pinchedConstant_map] at he
  have heq : (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) b)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (F.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) b))).edge := by
    change H.h.app (Opposite.op ⦋1⦌) (_, homotopyIntervalEdge.edge) = _
    rw [← pinchedConstant_one, ← pinchedConstant_one]
    exact he
  apply (isInvertibleEdge_congr heq).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

namespace DGModuleSquareData
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Y' Z : ModuleCategory A D}
variable (s : DGModuleSquareData A D W X Y Z) (m : Y ⟶ Y') (r : Y' ⟶ Z) (hr : m ≫ r = s.top)

/-- 零角以外の頂点は定値、零角の辺は終対象間の射なので全成分が可逆。 -/
lemma changeTopMiddleHomotopy_pointwise
    (hs : IsZeroVertex (squareVertex s.square 0 1))
    (ht : IsZeroVertex (squareVertex (s.changeTopMiddle m r hr).square 0 1))
    (k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌) :
    IsInvertibleEdge
      (simplicialHomotopyVertexEdge (s.changeTopMiddleHomotopy m r hr) k).toTruncated := by
  have hfix : (squareTriangle 1 ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫
      (s.changeTopMiddleHomotopy m r hr).h =
      CartesianMonoidalCategory.fst Δ[2] Δ[1] ≫ squareTriangle 1 ≫ s.square := by
    rw [changeTopMiddleHomotopy_lower, square_lower]
  rcases k with ⟨a, b⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
  fin_cases i <;> fin_cases j
  · have hv : (squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      IsInvertibleEdge (simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3)))
  · exact isIso_of_isTerminal hs.2.isTerminalHo ht.2.isTerminalHo _
  · have hv : (squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      IsInvertibleEdge (simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (1 : Fin 3)))
  · have hv : (squareTriangle.{max (u + 1) v} 1).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      by
        apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro k <;> fin_cases k <;> rfl
    exact (congrArg (fun k : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) _⦋0⦌ =>
      IsInvertibleEdge (simplicialHomotopyVertexEdge
        (s.changeTopMiddleHomotopy m r hr) k).toTruncated) hv).mp
      (fixed_map_vertex_invertible _ (squareTriangle 1) hfix
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))

/-- 左上の零角を変える実ホモトピーから四角形全体の関手同型を得る。 -/
def changeTopMiddleFunctorIso
    (hs : IsZeroVertex (squareVertex s.square 0 1))
    (ht : IsZeroVertex (squareVertex (s.changeTopMiddle m r hr).square 0 1)) :
    FunctorIso s.square (s.changeTopMiddle m r hr).square :=
  functorIsoOfPointwiseInvertibleHomotopy (s.changeTopMiddleHomotopy m r hr)
    (s.changeTopMiddleHomotopy_pointwise m r hr hs ht)

end DGModuleSquareData
end SerrePositivity.InfinityCategories
