module

public import SerrePositivity.InfinityCategories.F1.CocartesianPostcompositionTriangleComparison

/-!
概要：元の後合成 fiber の対角比較は、証明済みの同じ標準比較そのもので同値。
方針：fiber の包含と元の三角形への射の外延性で、両比較を厳密に同定する。
規約：第一辺だけの一致ではなく、元の第二三角形全体の一致を使う。
使われ方：元の固定成分比較と区間 Hom 比較の同値性を閉じる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)

/-- 元の対角 fiber 比較は、同じ元の fiber 上の標準合成比較そのもの。 -/
lemma cocartesianPostcompositionDiagonalComparison_eq_canonical :
    cocartesianPostcompositionDiagonalComparison F G b =
      cocartesianPostcompositionCanonicalComparison F G b := by
  apply vertexFiber_hom_ext
  apply compositionCorrespondence_hom_ext_triangle
  apply uncurry_injective
  simp only [Category.assoc]
  rw [cocartesianPostcompositionDiagonalComparison_triangle_uncurry,
    cocartesianPostcompositionCanonicalComparison_triangle_uncurry]

attribute [local instance] compositionCorrespondenceDiagonal_fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance : KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj
    (cocartesianIntervalPostcompositionFiber F G b)) := by
  letI := cocartesianIntervalPostcompositionFiber_kanComplex F G b
  infer_instance

/-- 元の後合成 fiber の同じ対角比較は、追加仮定なしに同値。 -/
lemma cocartesianPostcompositionDiagonalComparison_isQCatEquivalence :
    IsQCatEquivalence (cocartesianPostcompositionDiagonalComparison F G b) := by
  rw [cocartesianPostcompositionDiagonalComparison_eq_canonical]
  exact cocartesianPostcompositionCanonicalComparison_isQCatEquivalence F G b

end SerrePositivity.InfinityCategories
