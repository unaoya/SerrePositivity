module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTetrahedra
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ScaffoldFirstVertex

/-!
概要：元の三つの単位三単体は、全図式として同じ初期対象 F を厳密に持つ。
方針：標準三角柱の三単体の最初の頂点を計算し、元の入力三角形の始点へ戻す。
規約：全底を同時に保持。使われ方：三単体の共通の pointed 延長の初期条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 標準三角柱の元の三つの三単体。 -/
def trianglePrismDomainTetrahedron (i : Fin 3) :
    ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋3⦌ :=
  ((Δ[2] : SSet.{u}).σ i (SSet.yonedaEquiv (𝟙 Δ[2])), trianglePrismTime i)

/-- 三つとも最初の頂点は三角形の零頂点・時間零の同じ対。 -/
lemma trianglePrismDomainTetrahedron_first (i : Fin 3) :
    scaffoldFirstVertex 3 ≫ SSet.yonedaEquiv.symm (trianglePrismDomainTetrahedron.{u} i) =
      scaffoldFirstVertex 2 ≫ SSet.ι₀ := by
  apply SSet.yonedaEquiv.injective
  fin_cases i <;> apply Prod.ext <;> decide

variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の単位三単体は、標準三角柱の同じ三単体を全単位円柱で写したもの。 -/
lemma coherentColimitUnitTriangleTetrahedron_diagram (i : Fin 3) :
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T i) =
      SSet.yonedaEquiv.symm (trianglePrismDomainTetrahedron i) ≫
        coherentColimitUnitTrianglePrism B T := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- 三つの元の全単位三単体の最初の図式は、同じ F に厳密に一致する。 -/
lemma coherentColimitUnitTriangleTetrahedron_initial (i : Fin 3) :
    scaffoldFirstVertex 3 ≫
        SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T i) =
      SSet.const (functorVertex F) := by
  rw [coherentColimitUnitTriangleTetrahedron_diagram, ← Category.assoc,
    trianglePrismDomainTetrahedron_first, Category.assoc,
    coherentColimitUnitTrianglePrism_zero]
  have h : scaffoldFirstVertex.{u + 1} 2 =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    apply SSet.stdSimplex.ext
    intro k
    fin_cases k
    decide
  rw [h, Category.assoc]
  exact T.vertex_zero

end SerrePositivity.InfinityCategories.F2
