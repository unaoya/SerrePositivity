module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberComparisonJoin
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Derived.RebaseCocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-! # 標準 fiber の実際の coslice 比較辺

概要：標準 cofiber 余錐から元の fiber 余錐への辺を coslice 内に構成する。
方針：二つの span を同定し、比較 join 写像を curry する。
規約：両端の四角形を厳密に保持する。使われ方：β3 の標準 fiber の押し出し性。
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

/-- 二つの標準四角形は同じ span を持つ。 -/
lemma dgModuleFiberCofiberComparison_span (f : M ⟶ N) :
    pushoutSpan (dgModuleConeSquare A D (dgModuleFiberProjection A D f)) =
      pushoutSpan (dgModuleFiberSquare A D f) := by
  apply SSet.horn₂₀.isPushout.hom_ext
  · simp only [pushoutSpan, ← Category.assoc]
    rw [spanSquareBoundary_bottomEdge, dgModuleConeSquare_bottom]
    exact (dgModuleFiberSquare_bottom A D f).symm
  · simp only [pushoutSpan, ← Category.assoc]
    rw [spanSquareBoundary_leftEdge, dgModuleConeSquare_left]
    exact (dgModuleFiberSquare_left A D f).symm

/-- 元の fiber 余錐を標準 cofiber の span 上で読む。 -/
def dgModuleFiberCofiberTargetCocone (f : M ⟶ N) :
    JoinCocone (pushoutSpan
        (dgModuleConeSquare A D (dgModuleFiberProjection A D f))) :=
  rebaseCocone (dgModuleFiberCofiberComparison_span A D f)
    (pushoutCocone (dgModuleFiberSquare A D f))

/-- 比較 join 写像は span を固定する。 -/
lemma dgModuleFiberCofiberComparisonJoin_fixed (f : M ⟶ N) :
    joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ dgModuleFiberCofiberComparisonJoin A D f =
      pushoutSpan (dgModuleConeSquare A D (dgModuleFiberProjection A D f)) := by
  calc
    _ = (joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[0] ≫
        joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        dgModuleFiberCofiberComparisonJoin A D f := by
      rw [joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, dgModuleFiberCofiberComparisonJoin_face_one]
      exact (dgModuleConeCocone A D (dgModuleFiberProjection A D f)).property

/-- 標準 cofiber 余錐から元の fiber 余錐への実際の coslice 辺。 -/
def dgModuleFiberCofiberComparisonSliceEdge (f : M ⟶ N) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceUnder (pushoutSpan
      (dgModuleConeSquare A D (dgModuleFiberProjection A D f)))))
      (dgModuleConeCocone A D (dgModuleFiberProjection A D f))
      (dgModuleFiberCofiberTargetCocone A D f) where
  edge := SSet.yonedaEquiv
    (sliceUnderCurry (dgModuleFiberCofiberComparisonJoin A D f)
      (dgModuleFiberCofiberComparisonJoin_fixed A D f))
  src_eq := sliceUnderCurry_vertex_of_join _ _ 1 _
    (dgModuleFiberCofiberComparisonJoin_face_one A D f)
  tgt_eq := sliceUnderCurry_vertex_of_join _ _ 0 _
    (dgModuleFiberCofiberComparisonJoin_face_zero A D f)

end SerrePositivity.InfinityCategories
