module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberComparisonJoin
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonSlice
public import SerrePositivity.InfinityCategories.DGNerve.RebaseCone
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! # 標準 cofiber 錐から標準 fiber 錐への実際の辺

概要：貼り合わせた join 写像を curry し、同じ cospan 上の slice の比較辺を作る。
方針：二つの四角形の cospan を同定し、join の端点の等式から始点と終点を確認する。
規約：普遍性による選択に依存しない。使われ方：β3 の極限性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 二つの標準四角形は同じ cospan を持つ。 -/
lemma dgModuleCofiberFiberComparison_cospan (f : M ⟶ N) :
    pullbackCospan (dgModuleFiberSquare A D (moduleConeInr A D f)) =
      pullbackCospan (dgModuleConeSquare A D f) := by
  apply SSet.horn₂₂.isPushout.hom_ext
  · simp only [pullbackCospan, ← Category.assoc]
    rw [cospanSquareBoundary_rightEdge,
      dgModuleFiberSquare_right, dgModuleConeSquare_right]
  · simp only [pullbackCospan, ← Category.assoc]
    rw [cospanSquareBoundary_topEdge,
      dgModuleFiberSquare_top, dgModuleConeSquare_top]

/-- 元の cofiber 錐を標準 fiber の cospan 上で読む。 -/
def dgModuleCofiberFiberSourceCone (f : M ⟶ N) :
    JoinCone (pullbackCospan
      (dgModuleFiberSquare A D (moduleConeInr A D f))) :=
  rebaseCone (dgModuleCofiberFiberComparison_cospan A D f) (pullbackCone (dgModuleConeSquare A D f))

/-- 比較 join 写像は cospan を固定する。 -/
lemma dgModuleCofiberFiberComparisonJoin_fixed (f : M ⟶ N) :
    joinInr (Δ[1] : SSet) (SSet.horn 2 2) ≫ dgModuleCofiberFiberComparisonJoin A D f =
      pullbackCospan (dgModuleFiberSquare A D (moduleConeInr A D f)) := by
  calc
    _ = (joinInr (Δ[0] : SSet) (SSet.horn 2 2) ≫
        joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet))) ≫
        dgModuleCofiberFiberComparisonJoin A D f := by
      rw [joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, dgModuleCofiberFiberComparisonJoin_face_zero]
      exact (dgModuleFiberCone A D (moduleConeInr A D f)).property

/-- 元の錐から標準 fiber 錐への、明示的な slice 比較辺。 -/
def dgModuleCofiberFiberComparisonSliceEdge (f : M ⟶ N) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceOver (pullbackCospan
      (dgModuleFiberSquare A D (moduleConeInr A D f)))))
      (dgModuleCofiberFiberSourceCone A D f)
      (dgModuleFiberCone A D (moduleConeInr A D f)) where
  edge := SSet.yonedaEquiv
    (sliceOverCurry (dgModuleCofiberFiberComparisonJoin A D f)
      (dgModuleCofiberFiberComparisonJoin_fixed A D f))
  src_eq := sliceOverCurry_vertex_of_join _ _ 1 _ (dgModuleCofiberFiberComparisonJoin_face_one A D
    f)
  tgt_eq := sliceOverCurry_vertex_of_join _ _ 0 _ (dgModuleCofiberFiberComparisonJoin_face_zero A
    D f)

end SerrePositivity.InfinityCategories
