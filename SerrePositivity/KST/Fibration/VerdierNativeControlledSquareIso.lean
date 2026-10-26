module
public import SerrePositivity.KST.Fibration.VerdierNativeControlledSquarePrism

/-!
概要：実 (9b) 欠面から元の指定 Verdier 四角形へ、同じ対角固定四角柱の全関手同型を構成する。
方針：同じ制御上側三角柱と元の下側の定値三角柱を全共有対角で貼る。
規約：元の実充填・全二胞体を保持し、新しい存在仮定を取らない。
使われ方：K-6 c4 の有限始端照合後の元の四角形への実復帰。
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
variable (d : VerdierDiagram.{u}) (t : (Δ[1] : SSet.{u + 1}) _⦋0⦌)

/-- 概要：同じ全四角柱は、元の指定上側三角柱を全パラメーターで厳密回収する。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_upper :
    (squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierNativeControlledSquarePrism d t).h =
      (verdierNativeControlledUpperPrism d t).h := squareHomotopyOfTriangleHomotopies_upper _ _ _

/-- 概要：同じ全四角柱は、元の指定下側二胞体を全パラメーターで厳密固定する。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_lower :
    (squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ (verdierNativeControlledSquarePrism d t).h =
      fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
        (squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))) :=
  squareHomotopyOfTriangleHomotopies_lower _ _ _

/-- 概要：全四角柱の上側の縦辺は、同じ元の可逆三角柱の辺へ厳密に戻る。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_upper_edge (k : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (verdierNativeControlledSquarePrism d t)
      ((squareTriangle 0).app (Opposite.op ⦋0⦌) k)).edge =
        (simplicialHomotopyVertexEdge (verdierNativeControlledUpperPrism d t) k).edge := by
  have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 k), homotopyIntervalEdge.edge))
      (verdierNativeControlledSquarePrism_upper d t)
  change (verdierNativeControlledSquarePrism d t).h.app (Opposite.op ⦋1⦌)
    ((squareTriangle 0).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k),
      homotopyIntervalEdge.edge) = _ at he
  rw [σ_naturality_apply] at he
  exact he

/-- 概要：全四角柱の固定した下側の縦辺は、元の同じ頂点の恒等辺である。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_lower_edge (k : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (verdierNativeControlledSquarePrism d t)
      ((squareTriangle 1).app (Opposite.op ⦋0⦌) k)).edge =
        (Truncated.Edge.id (X := (truncation 2).obj SpaceInfinity.{u})
          ((squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))).app
            (Opposite.op ⦋0⦌) k)).edge := by
  have he := congrArg (fun f : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    f.app (Opposite.op ⦋1⦌) (((Δ[2] : SSet.{u + 1}).σ 0 k), homotopyIntervalEdge.edge))
      (verdierNativeControlledSquarePrism_lower d t)
  change (verdierNativeControlledSquarePrism d t).h.app (Opposite.op ⦋1⦌)
    ((squareTriangle 1).app (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k),
      homotopyIntervalEdge.edge) =
        (squareTriangle 1 ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0))).app
          (Opposite.op ⦋1⦌) ((Δ[2] : SSet.{u + 1}).σ 0 k) at he
  rw [σ_naturality_apply, σ_naturality_apply] at he
  exact he

/-- 概要：同じ全四角柱の全ての縦辺は、四頂点で可逆である。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_pointwise :
    ∀ k : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge (verdierNativeControlledSquarePrism d t) k).toTruncated := by
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
  · exact (isInvertibleEdge_congr (verdierNativeControlledSquarePrism_upper_edge d t a)).mpr
      (verdierNativeControlledUpperPrism_pointwise d t a)
  · apply (isInvertibleEdge_congr (verdierNativeControlledSquarePrism_lower_edge d t a)).mpr
    change IsIso (Truncated.HomotopyCategory.homMk (Truncated.Edge.id _))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance

/-- 概要：同じ元の全四角柱の辺そのものは、関手単体集合で可逆である。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquarePrism_isInvertible :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (verdierNativeControlledSquarePrism d t)) :=
  functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise _ (verdierNativeControlledSquarePrism_pointwise d t)

/-- 概要：元の全指定四角形へ終わる、同じ実四角柱の全関手同型。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
def verdierNativeControlledSquarePrismIso : FunctorIso (verdierNativeControlledSquare d t)
    (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  functorIsoOfPointwiseInvertibleHomotopy _ (verdierNativeControlledSquarePrism_pointwise d t)

/-- 概要：同じ元の全四角柱の同型は、指定した全四角形の引き戻し性を両方向に保つ。
方針：同じ実制御三角柱と元の下側の貼り合わせを使う。
規約：新しい存在仮定なし。使われ方：指定有限始端照合後の全四角形比較。 -/
theorem verdierNativeControlledSquare_isPullback_iff :
    IsPullbackSquare (verdierNativeControlledSquare d t) ↔
      IsPullbackSquare (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  ⟨fun h => h.of_functorIso (verdierNativeControlledSquarePrismIso d t),
    fun h => h.of_functorIso (verdierNativeControlledSquarePrismIso d t).symm⟩

end SerrePositivity.KST.Fibration
