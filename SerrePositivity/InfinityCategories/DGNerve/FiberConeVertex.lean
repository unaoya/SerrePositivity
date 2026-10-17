module
public import SerrePositivity.InfinityCategories.DGNerve.FiberSquare

/-! # 標準 fiber の join 錐の頂点

概要：標準四角形から作った JoinCone の頂点が標準 fiber の頂点そのものであると示す。
方針：錐の左包含を下側三角形の最初の頂点で表し、構成した二単体の対象を評価する。
規約：HTT Definition 1.2.13.4。使われ方：N7c の境界充填と N7e の頂点の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped Simplicial

/-- 概要：cospan の錐の左包含は下側三角形の最初の頂点の包含。
方針：標準単体の join の左頂点の式と joinMap の包含の自然性を使う。
規約：HTT §1.2.13。使われ方：JoinCone の頂点の計算。 -/
lemma cospanConeTriangleLeft_first :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫ cospanConeTriangleLeft.{u} =
      joinInl Δ[0] (SSet.horn 2 2 : SSet.{u}) := by
  have hv : joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso 0 1).hom =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) := joinStdSimplexIso_inl_vertex 1
  unfold cospanConeTriangleLeft
  rw [← hv, Category.assoc, Iso.hom_inv_id_assoc, joinInl_joinMap, Category.id_comp]

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 fiber の錐の頂点は標準 fiber の dg nerve の頂点。
方針：左包含を下側三角形の最初の頂点へ移し、chain map の三角形の対象を評価する。
規約：HTT Definition 1.2.13.4。使われ方：fiber 錐の極限対象の同定。 -/
lemma standardFiberCone_vertex (g : B ⟶ D) (h : C ⟶ D) :
    (standardFiberCone g h).vertex = Simplex.vertex (pullbackFiber g h) := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] (SSet.horn 2 2 : SSet.{u + 1}) ≫
    (cospanConeSquareIso.hom ≫ standardFiberSquare g h)) = _
  rw [← cospanConeTriangleLeft_first]
  simp only [Category.assoc]
  rw [← Category.assoc cospanConeTriangleLeft cospanConeSquareIso.hom (standardFiberSquare g h),
    cospanConeSquareIso_left, standardFiberSquare_lower, ← SSet.yonedaEquiv_naturality,
    Equiv.apply_symm_apply]
  apply Simplex.vertexEquiv.injective
  rfl

end SerrePositivity.InfinityCategories.DGNerve
