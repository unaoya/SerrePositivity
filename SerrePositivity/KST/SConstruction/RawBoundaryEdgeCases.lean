module
public import SerrePositivity.KST.SConstruction.RawBoundaryDiagonalEdges

/-! # 元の境界商の全ての辺の対象辺への帰着
概要：元の境界商の辺の基本亜群の類は恒等射または元の object S₁ の辺の類となる。
方針：商の次数ごとの二つの代表と元の対角の辺の三角形を使う。
規約：元の正方形と対象の選択を保つ。使われ方：対象 K 類による零次群の生成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 商の点から来る辺は元の基点の退化辺である。 -/
lemma rawBoundary_point_edge (X : StableModel.{u}) (p : (𝟙_ SSet.{u}) _⦋1⦌) :
    (boundaryReducedRealization 0 X).hom.app (Opposite.op ⦋1⦌) p =
      (boundaryReducedRealization 0 X).right.σ 0 (boundaryReducedRealization 0 X).basepoint := by
  cases p
  exact ConcreteCategory.congr_hom
    ((boundaryReducedRealization 0 X).hom.naturality (SimplexCategory.σ (0 : Fin 1)).op) PUnit.unit

/-- 元の退化辺の境界定数単体は元の定数単体。 -/
lemma rawBoundaryLoopSimplex_degenerate (X : StableModel.{u}) :
    rawBoundaryLoopSimplex X ((boundaryReducedRealization 0 X).right.σ 0
      (boundaryReducedRealization 0 X).basepoint) = .const := by
  apply RelativeMorphism.ext
  change SSet.yonedaEquiv.symm ((boundaryReducedRealization 0 X).right.σ 0
    (boundaryReducedRealization 0 X).basepoint) = SSet.const _
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero, SSet.comp_const]

/-- 商の点から来る辺は基本亜群で恒等射となる。 -/
lemma rawBoundaryPath_point (X : StableModel.{u}) (p : (𝟙_ SSet.{u}) _⦋1⦌) :
    rawBoundaryPath X ((boundaryReducedRealization 0 X).hom.app (Opposite.op ⦋1⦌) p) =
      𝟙 (boundaryFundamentalBasepoint X) := by
  rw [rawBoundary_point_edge, rawBoundaryPath, rawBoundaryLoopSimplex_degenerate,
    fundamentalLoopEdge_const, SSet.Truncated.HomotopyCategory.homMk_id]
  exact (FreeGroupoid.of (hoFunctor.obj (boundaryReducedRealization 0 X).right)).map_id _

/-- 元の境界商の任意の辺の類は、恒等射または元の object S₁ の辺の類に等しい。 -/
lemma rawBoundaryPath_cases (X : StableModel.{u})
    (e : (boundaryReducedRealization 0 X).right _⦋1⦌) :
    rawBoundaryPath X e = 𝟙 (boundaryFundamentalBasepoint X) ∨
      ∃ d : (objectSConstruction X.carrier) _⦋1⦌,
        rawBoundaryPath X e = objectBoundaryPath X d := by
  rcases rawCofiber_simplex_cases (zeroDirectionsFatBoundary 1 X).ι
      (Opposite.op ⦋1⦌) e with ⟨b, rfl⟩ | ⟨p, rfl⟩
  · let a : (coreSConstruction 1 X.carrier) _⦋1⦌ :=
      (iteratedSRealizationCoordinateIso 0 X).inv.app (Opposite.op ⦋1⦌) b
    have hv := ConcreteCategory.congr_hom (NatTrans.congr_app
      (iteratedSRealizationCoordinateIso 0 X).inv_hom_id (Opposite.op ⦋1⦌)) b
    change (iteratedSRealizationCoordinateIso 0 X).hom.app (Opposite.op ⦋1⦌) a = b at hv
    have he := congrArg ((boundaryReductionQuotient 0 X).app (Opposite.op ⦋1⦌)) hv
    refine Or.inr ⟨((coreSConstruction 1 X.carrier).δ 1 a).val, ?_⟩
    exact (congrArg (rawBoundaryPath X) he.symm).trans (rawBoundaryPath_diagonal X a)
  · exact Or.inl (rawBoundaryPath_point X p)

end SerrePositivity.KST.SConstruction
