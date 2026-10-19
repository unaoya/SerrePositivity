module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonJoin
public import SerrePositivity.InfinityCategories.Derived.ComplexEdgeCalculus
public import SerrePositivity.InfinityCategories.Derived.RebaseCocone
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-! # 標準 fiber の実際の coslice 比較辺

概要：標準 cofiber 余錐から元の fiber 余錐への辺を coslice 内に構成する。
方針：二つの span を同定し、比較 join 写像を curry する。
規約：両端の四角形を厳密に保持する。使われ方：D7 の標準 fiber の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

/-- Coslice への curry の端点を join の端点への制限から回収する。 -/
lemma sliceUnderCurry_vertex_of_join {K X : SSet.{u}} {p : K ⟶ X}
    (F : join K (Δ[1] : SSet.{u}) ⟶ X) (hF : joinInl K Δ[1] ≫ F = p)
    (i : Fin 2) (c : JoinCocone p)
    (hc : joinMap (𝟙 K) (SSet.stdSimplex.δ i) ≫ F = c.val) :
    (sliceUnder p).δ i (SSet.yonedaEquiv (sliceUnderCurry F hF)) = c := by
  have hm : SSet.stdSimplex.δ i ≫ sliceUnderCurry F hF = SSet.yonedaEquiv.symm c := by
    rw [sliceUnderCurry_precomp]
    let d : JoinCocone p := ⟨joinMap (𝟙 K) (SSet.stdSimplex.δ i) ≫ F, by
      rw [← Category.assoc, joinInl_joinMap, Category.id_comp, hF]⟩
    have hd : d = c := Subtype.ext hc
    exact (sliceUnderCurry_yoneda 0 d).trans (congrArg SSet.yonedaEquiv.symm hd)
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hm]
  exact (SSet.yonedaEquiv (X := sliceUnder p)).apply_symm_apply c

variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 二つの標準四角形は同じ span を持つ。 -/
lemma fiberCofiberComparison_span (g : B ⟶ D) (h : C ⟶ D) :
    pushoutSpan (standardCofiberSquare (pullbackProjectionB g h) (pullbackProjectionC g h)) =
      pushoutSpan (standardFiberSquare g h) := by
  apply SSet.horn₂₀.isPushout.hom_ext
  · simp only [pushoutSpan, ← Category.assoc]
    rw [spanSquareBoundary_bottomEdge, standardCofiberSquare_bottom]
    exact (derived_standardFiberSquare_bottom g h).symm
  · simp only [pushoutSpan, ← Category.assoc]
    rw [spanSquareBoundary_leftEdge, standardCofiberSquare_left]
    exact (derived_standardFiberSquare_left g h).symm

/-- 元の fiber 余錐を標準 cofiber の span 上で読む。 -/
def fiberCofiberTargetCocone (g : B ⟶ D) (h : C ⟶ D) :
    JoinCocone (pushoutSpan (standardCofiberSquare
      (pullbackProjectionB g h) (pullbackProjectionC g h))) :=
  rebaseCocone (fiberCofiberComparison_span g h) (pushoutCocone (standardFiberSquare g h))

/-- 比較 join 写像は span を固定する。 -/
lemma fiberCofiberComparisonJoin_fixed (g : B ⟶ D) (h : C ⟶ D) :
    joinInl (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ≫ fiberCofiberComparisonJoin g h =
      pushoutSpan (standardCofiberSquare (pullbackProjectionB g h) (pullbackProjectionC g h)) := by
  calc
    _ = (joinInl (SSet.horn 2 0 : SSet.{u + 1}) Δ[0] ≫
        joinMap (𝟙 (SSet.horn 2 0 : SSet.{u + 1})) (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        fiberCofiberComparisonJoin g h := by
      rw [joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, fiberCofiberComparisonJoin_face_one]
      exact (standardCofiberCocone _ _).property

/-- 標準 cofiber 余錐から元の fiber 余錐への実際の coslice 辺。 -/
def fiberCofiberComparisonSliceEdge (g : B ⟶ D) (h : C ⟶ D) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceUnder (pushoutSpan
      (standardCofiberSquare (pullbackProjectionB g h) (pullbackProjectionC g h)))))
      (standardCofiberCocone (pullbackProjectionB g h) (pullbackProjectionC g h))
      (fiberCofiberTargetCocone g h) where
  edge := SSet.yonedaEquiv
    (sliceUnderCurry (fiberCofiberComparisonJoin g h) (fiberCofiberComparisonJoin_fixed g h))
  src_eq := sliceUnderCurry_vertex_of_join _ _ 1 _ (fiberCofiberComparisonJoin_face_one g h)
  tgt_eq := sliceUnderCurry_vertex_of_join _ _ 0 _ (fiberCofiberComparisonJoin_face_zero g h)

end SerrePositivity.InfinityCategories
