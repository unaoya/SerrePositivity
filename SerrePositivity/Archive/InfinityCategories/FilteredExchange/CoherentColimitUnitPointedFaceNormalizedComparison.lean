module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFaceIso

/-!
概要：元の指定二単体へ底を揃えた後も、面の指定比較とその合成の値を保持する。
方針：制限先の可縮性と元の指定同型の写像の合成則を使う。
規約：実頂点と指定同型の等式。使われ方：共有二面の比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  (S : (Δ[2] : SSet.{u + 1}) ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S)
local notation "m" => coherentColimitUnitPointedFaceMap B T k j hj S hS
local notation "hc" => leftUnstraighteningSimplexChoiceSpace_isContractibleKan F 2
  (functorSimplexDiagram S) (coherentColimitUnitPointedFace_initial B T k j hj S hS)

/-- 元の指定比較は、底を揃えた元の二単体の同じ選択済み比較に値まで一致する。 -/
lemma coherentColimitUnitPointedFaceComparison_normalized
    {x y : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e m = (hc).vertexIso ((m).app (Opposite.op ⦋0⦌) x)
      ((m).app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible hc e m

/-- 元の二つの比較の面制限の合成も、底を揃えた同じ直接比較そのもの。 -/
lemma coherentColimitUnitPointedFaceComparison_normalized_trans
    {x y z : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌}
    (e : VertexIso x y) (f : VertexIso y z) :
    VertexIso.map e m ≪≫ VertexIso.map f m =
      (hc).vertexIso ((m).app (Opposite.op ⦋0⦌) x) ((m).app (Opposite.op ⦋0⦌) z) := by
  rw [← vertexIso_map_trans]
  exact coherentColimitUnitPointedFaceComparison_normalized B T k j hj S hS (e ≪≫ f)

end SerrePositivity.InfinityCategories.F2
