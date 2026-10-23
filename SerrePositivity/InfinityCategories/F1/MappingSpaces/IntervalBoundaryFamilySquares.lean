module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalBoundaryFamilyContractible
public import SerrePositivity.InfinityCategories.F1.Transport.SquareSpace

/-!
概要：実際の区間族の境界固定 lift を元の可換四角形空間へ実現する。
方針：普遍 lift と分類区間の二射影を引き戻しへ束ねる。
規約：境界上の pointed space への射も分類区間も厳密に保持する。
使われ方：可縮な区間族と実際の表現空間の境界 fiber を結ぶ比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：実際の境界固定 lift 族を元の区間の可換四角形の族へ写す。
方針：相対内部 Hom の普遍 lift と分類区間から引き戻しへの射を作る。
規約：全高次単体に対する射。
使われ方：表現空間の境界 fiber への比較の周囲の射。 -/
def intervalFixedBoundaryFamilySquareMap {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) :
    intervalFixedBoundaryFamilySpace p g₀ g₁ ⟶ transportSquareSpace p :=
  pullback.lift
    (relativeBoundaryFamilyCurry (intervalBoundaryRelativeHom p)
      (intervalFixedBoundaryFamilyData p g₀ g₁))
    (relativeBoundaryFamilyProjection (intervalBoundaryRelativeHom p)
      (intervalFixedBoundaryFamilyData p g₀ g₁) ≫ cylinderIntervalDiagramι s t) (by
        rw [relativeBoundaryFamilyCurry_base]
        dsimp only [intervalFixedBoundaryFamilyData, intervalBoundaryFamilyData]
        rw [relativeBoundaryFamilyData_snd]
        simp only [Category.assoc])

/-- 概要：四角形の実現から普遍 pointed space 値 lift を厳密に回収する。
方針：引き戻しへの lift の第一射影。
規約：元の全空間 E 上の実際の射を保持する。
使われ方：境界の全空間側の固定条件。 -/
lemma intervalFixedBoundaryFamilySquareMap_pointed {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) :
    intervalFixedBoundaryFamilySquareMap p g₀ g₁ ≫ transportSquarePointed p =
      relativeBoundaryFamilyCurry (intervalBoundaryRelativeHom p)
        (intervalFixedBoundaryFamilyData p g₀ g₁) := pullback.lift_fst _ _ _

/-- 概要：四角形の実現の分類図式は元の分類区間の包含。
方針：引き戻しへの lift の第二射影。
規約：区間内部の分類図式を選び直さない。
使われ方：底側の境界固定条件と逆比較の回収。 -/
lemma intervalFixedBoundaryFamilySquareMap_diagram {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) :
    intervalFixedBoundaryFamilySquareMap p g₀ g₁ ≫ transportSquareDiagram p =
      relativeBoundaryFamilyProjection (intervalBoundaryRelativeHom p)
        (intervalFixedBoundaryFamilyData p g₀ g₁) ≫ cylinderIntervalDiagramι s t :=
  pullback.lift_snd _ _ _

/-- 概要：実現した四角形の全空間側の両端は指定した写像を厳密に保つ。
方針：相対 lift の境界条件とデータの定値性。
規約：パラメーターの全次数で境界を定値に固定する。
使われ方：実際の境界制限の fiber への持ち上げ。 -/
lemma intervalFixedBoundaryFamilySquareMap_boundary {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection s)
    (g₁ : vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ⟶
      vertexFiber pointedSpaceProjection t) :
    (intervalFixedBoundaryFamilySquareMap p g₀ g₁ ≫ transportSquarePointed p) ≫
        (pre (intervalFiberEndpointInclusion p)).app _ =
      SSet.const (functorVertex (intervalBoundaryPointedMap g₀ g₁)) := by
  rw [intervalFixedBoundaryFamilySquareMap_pointed, relativeBoundaryFamilyCurry_boundary]
  dsimp only [intervalFixedBoundaryFamilyData, intervalBoundaryFamilyData]
  rw [relativeBoundaryFamilyData_fst, SSet.comp_const]

end SerrePositivity.InfinityCategories
