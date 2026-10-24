module
public import SerrePositivity.KST.Fibration.VerdierFullSSquarePrism
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-!
概要：元の上下二胞体を保持する全四角柱を、その指定辺による全関手同型に束ねる。
方針：三角形ごとの縦辺を元の三角柱へ回収し、四頂点を両三角形で覆う。
規約：下側全二胞体の固定と上側の指定比較を保つ。商核四角形との同定は別工程。
使われ方：K-6 c4 の全四角形比較の Verdier 側と、同じ引き戻し性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : VerdierDiagram.{u})

/-- 同じ全四角柱は、元の指定上側三角柱を全パラメーターで厳密回収する。 -/
theorem verdierFullSSquarePrism_upper :
    (squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSSquarePrism d).h =
      (verdierFullSUpperPrism d).h := squareHomotopyOfTriangleHomotopies_upper _ _ _

/-- 同じ全四角柱は、元の指定下側二胞体を全パラメーターで厳密固定する。 -/
theorem verdierFullSSquarePrism_lower :
    (squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierFullSSquarePrism d).h =
      fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
        (squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))) :=
  squareHomotopyOfTriangleHomotopies_lower _ _ _

/-- 全四角柱の上側の縦辺は、同じ元の可逆三角柱の辺へ厳密に戻る。 -/
theorem verdierFullSSquarePrism_upper_edge (k : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (verdierFullSSquarePrism d)
      ((squareTriangle 0).app (Opposite.op ⦋0⦌) k)).edge =
        (simplicialHomotopyVertexEdge (verdierFullSUpperPrism d) k).edge := by
  have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 k), homotopyIntervalEdge.edge))
      (verdierFullSSquarePrism_upper d)
  change (verdierFullSSquarePrism d).h.app (Opposite.op ⦋1⦌)
    ((squareTriangle 0).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k),
      homotopyIntervalEdge.edge) = _ at he
  rw [σ_naturality_apply] at he
  exact he

/-- 全四角柱の固定した下側の縦辺は、元の同じ頂点の恒等辺である。 -/
theorem verdierFullSSquarePrism_lower_edge (k : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (verdierFullSSquarePrism d)
      ((squareTriangle 1).app (Opposite.op ⦋0⦌) k)).edge =
        (Truncated.Edge.id (X := (truncation 2).obj SpaceInfinity.{u})
          ((squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))).app
            (Opposite.op ⦋0⦌) k)).edge := by
  have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 k), homotopyIntervalEdge.edge))
      (verdierFullSSquarePrism_lower d)
  change (verdierFullSSquarePrism d).h.app (Opposite.op ⦋1⦌)
    ((squareTriangle 1).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k),
      homotopyIntervalEdge.edge) =
        (squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))).app
          (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k) at he
  rw [σ_naturality_apply, σ_naturality_apply] at he
  exact he

/-- 同じ全四角柱の全ての縦辺は、四頂点で可逆である。 -/
theorem verdierFullSSquarePrism_pointwise :
    ∀ k : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge (verdierFullSSquarePrism d) k).toTruncated := by
  intro k
  have hc : (∃ a, k = (squareTriangle 0).app (Opposite.op ⦋0⦌) a) ∨
      (∃ a, k = (squareTriangle 1).app (Opposite.op ⦋0⦌) a) := by
    rcases k with ⟨k₀, k₁⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₀
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k₁
    fin_cases i <;> fin_cases j
    · exact Or.inl ⟨stdSimplex.obj₀Equiv.symm 0, rfl⟩
    · exact Or.inl ⟨stdSimplex.obj₀Equiv.symm 1, rfl⟩
    · exact Or.inr ⟨stdSimplex.obj₀Equiv.symm 1, rfl⟩
    · exact Or.inl ⟨stdSimplex.obj₀Equiv.symm 2, rfl⟩
  rcases hc with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (isInvertibleEdge_congr (verdierFullSSquarePrism_upper_edge d a)).mpr
      (verdierFullSUpperPrism_pointwise d a)
  · apply (isInvertibleEdge_congr (verdierFullSSquarePrism_lower_edge d a)).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance

/-- 同じ元の全四角柱の辺そのものは、関手単体集合で可逆である。 -/
theorem verdierFullSSquarePrism_isInvertible :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (verdierFullSSquarePrism d)) :=
  functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise _ (verdierFullSSquarePrism_pointwise d)

/-- 元の全指定四角形へ終わる、同じ実四角柱の全関手同型。 -/
def verdierFullSSquarePrismIso : FunctorIso (verdierFullSTransportedSquare d)
    (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  functorIsoOfPointwiseInvertibleHomotopy _ (verdierFullSSquarePrism_pointwise d)

/-- 同じ元の全四角柱の同型は、指定した全四角形の引き戻し性を両方向に保つ。 -/
theorem verdierFullSTransportedSquare_isPullback_iff :
    IsPullbackSquare (verdierFullSTransportedSquare d) ↔
      IsPullbackSquare (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  ⟨fun h => h.of_functorIso (verdierFullSSquarePrismIso d),
    fun h => h.of_functorIso (verdierFullSSquarePrismIso d).symm⟩

end SerrePositivity.KST.Fibration
