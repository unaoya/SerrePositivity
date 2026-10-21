module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedZeroFaceSection
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronSides

/-!
概要：元の第零面の初期値を第一辺の終点へ同定し、実制限の指定比較を保つ。
方針：全パラメータの厳密な式と、可変初期値の全延長空間の可縮性を使う。
規約：第一辺や元の上下単位三角形を選び直さない。使われ方：三関係の第零面。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 第零面の可変初期値は、元の全三単体の第一辺の終点評価そのもの。 -/
lemma coherentColimitUnitPointedZeroFace_boundary_firstEdge (k : Fin 3) :
    (coherentColimitUnitPointedZeroFaceFamily B T k).boundary =
      ((stdSimplex.δ (0 : Fin 2) ▷ leftUnstraightening F) ▷
        coherentColimitUnitPointedTetrahedronChoice B T k) ≫
      (((stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ▷
        leftUnstraightening F) ▷ coherentColimitUnitPointedTetrahedronChoice B T k) ≫
        coherentColimitUnitPointedTetrahedronUniversalLift B T k := by
  have he : scaffoldFirstVertex.{u + 1} 2 ≫ stdSimplex.δ (0 : Fin 4) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫
        stdSimplex.δ (3 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro x
    fin_cases x
    rfl
  change (((scaffoldFirstVertex 2 ≫ stdSimplex.δ (0 : Fin 4)) ▷ _) ▷ _) ≫ _ = _
  rw [he, comp_whiskerRight, comp_whiskerRight, Category.assoc]

/-- 中央の第零面の底は、元の最後の辺の下単位三角形の同じ全族。 -/
lemma coherentColimitUnitPointedZeroFace_middle_diagram :
    (coherentColimitUnitPointedZeroFaceFamily B T 1).diagram =
      fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B)
        (coherentColimitUnitPointedTetrahedronChoice B T 1) ≫
          functorSimplexDiagram (coherentColimitUnitLowerTriangle B r).diagram := by
  change _ ≫ functorSimplexDiagram _ = _
  rw [coherentColimitUnitTetrahedron_upper_last, Equiv.symm_apply_apply]

/-- 最後の第零面の底は、元の最後の辺の上単位三角形の同じ全族。 -/
lemma coherentColimitUnitPointedZeroFace_last_diagram :
    (coherentColimitUnitPointedZeroFaceFamily B T 2).diagram =
      fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B)
        (coherentColimitUnitPointedTetrahedronChoice B T 2) ≫
          functorSimplexDiagram (coherentColimitUnitUpperTriangle B r).diagram := by
  change _ ≫ functorSimplexDiagram _ = _
  rw [coherentColimitUnitTetrahedron_lower_last, Equiv.symm_apply_apply]

/-- 元の全三単体の指定比較を第零面の実制限へ移すと、同じ選択済み比較となる。 -/
lemma coherentColimitUnitPointedZeroFaceSection_comparison (k : Fin 3)
    {x y : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (coherentColimitUnitPointedZeroFaceSection B T k) =
      (coherentColimitUnitPointedZeroFaceFamily_contractible B T k).vertexIso
        ((coherentColimitUnitPointedZeroFaceSection B T k).app (Opposite.op ⦋0⦌) x)
        ((coherentColimitUnitPointedZeroFaceSection B T k).app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible
    (coherentColimitUnitPointedZeroFaceFamily_contractible B T k) e _

end SerrePositivity.InfinityCategories.F2
