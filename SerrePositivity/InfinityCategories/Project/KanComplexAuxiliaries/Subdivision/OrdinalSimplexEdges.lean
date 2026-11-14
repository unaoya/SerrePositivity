module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：標準単体の順序辺と三角形を、元の単体の辺の合成関係へ移す。
方針：標準の二単体の三面を直接計算し、元の単体の Yoneda 射で後合成する。
規約：合成は Mathlib の左から右の向き。使われ方：edgewise 解像の三単体の向きの検算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.SimplexEdges
end SerrePositivity.KST.Spectra.SimplexEdges
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.SimplexEdges

/-- 標準単体内の、指定した順序付き二頂点を結ぶ元の辺。 -/
def edge {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (Δ[n] : SSet.{u}).Edge (stdSimplex.obj₀Equiv.symm i) (stdSimplex.obj₀Equiv.symm j) :=
  SSet.Edge.mk (stdSimplex.edge n i j h)
    (by apply stdSimplex.obj₀Equiv.injective; rfl)
    (by apply stdSimplex.obj₀Equiv.injective; rfl)

/-- 標準の順序辺の二頂点の像は、指定した始点と終点。 -/
lemma edgeMap_vertex {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (t : Fin 2) :
    (SSet.yonedaEquiv.symm (stdSimplex.edge.{u} n i j hij)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm t) = stdSimplex.obj₀Equiv.symm (if t = 0 then i else j) := by
  apply stdSimplex.obj₀Equiv.injective
  fin_cases t <;> rfl

/-- 三つの順序付き頂点の標準三角形は、元の三辺の合成を与える。 -/
def compStruct {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge.{u} i j hij) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge j k hjk) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge i k (hij.trans hjk)) :=
  SSet.Edge.CompStruct.mk (stdSimplex.triangle i j k hij hjk)
    (by apply stdSimplex.ext; intro r; fin_cases r <;> rfl)
    (by apply stdSimplex.ext; intro r; fin_cases r <;> rfl)
    (by apply stdSimplex.ext; intro r; fin_cases r <;> rfl)

/-- 元の三単体の四つの順序辺は、同じホモトピー圏内で三段の合成式を満たす。 -/
lemma tetrahedron_relation {X : SSet.{u}} (a : X _⦋3⦌) :
    SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 4) 1 (by decide)).map
        (SSet.yonedaEquiv.symm a)) ≫
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (1 : Fin 4) 2 (by decide)).map
        (SSet.yonedaEquiv.symm a)) ≫
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (2 : Fin 4) 3 (by decide)).map
        (SSet.yonedaEquiv.symm a)) =
      SSet.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 4) 3 (by decide)).map
        (SSet.yonedaEquiv.symm a)) := by
  rw [← Category.assoc, SSet.HomotopyCategory.homMk_comp_homMk
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 4) 1 2 (by decide) (by decide)).map (SSet.yonedaEquiv.symm a))]
  exact SSet.HomotopyCategory.homMk_comp_homMk
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 4) 2 3 (by decide) (by decide)).map (SSet.yonedaEquiv.symm a))

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.compStruct := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.edge := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.edgeMap_vertex := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edgeMap_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.tetrahedron_relation := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.tetrahedron_relation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.compStruct._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.compStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.compStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.compStruct._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.edge._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.edge._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.tetrahedron_relation._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.tetrahedron_relation._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.tetrahedron_relation._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.tetrahedron_relation._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.tetrahedron_relation._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.tetrahedron_relation._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.SimplexEdges.tetrahedron_relation._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.tetrahedron_relation._proof_4
