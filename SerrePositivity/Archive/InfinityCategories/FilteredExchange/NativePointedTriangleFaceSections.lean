module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionCurryRestriction

/-!
概要：元の全三角形の指定比較を、各面上の切断族の指定関手同型として表示する。
方針：同じ延長空間からの制限と相対 curry を合成し、native 側と元の側の頂点を同定する。
規約：三面すべてに同じ指定比較を用いる。使われ方：実際の二脚と共通終点の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A : SSet.{u + 1}} (D : (Δ[2] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (W : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
  (hW : W ≫ pointedSpaceProjection = fst Δ[2] A ≫ D) (face : Fin 3)

include hW in
/-- 同じ三角形の面の全族は、元の面の図式を被覆する。 -/
lemma pointedTriangleFace_projection :
    ((stdSimplex.δ face ▷ A) ≫ W) ≫ pointedSpaceProjection =
      fst Δ[1] A ≫ (stdSimplex.δ face ≫ D) := by
  rw [Category.assoc, hW, ← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 三角形の面への元の全制限を、切断のパラメータ族へ表示する。 -/
def pointedTriangleFaceSections : A ⟶
    relativeFunctorSpace pointedSpaceProjection (stdSimplex.δ face ≫ D) :=
  relativeFunctorCurry ((stdSimplex.δ face ▷ A) ≫ W)
    (pointedTriangleFace_projection D W hW face)

/-- 相対 curry の展開は、同じ面の元の全円柱を厳密に回収する。 -/
lemma pointedTriangleFaceSections_uncurry :
    relativeFunctorUncurry (pointedTriangleFaceSections D W hW face) =
      (stdSimplex.δ face ▷ A) ≫ W :=
  relativeFunctorUncurry_curry _ _

variable {K : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌)
local notation "Dk" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "N" => nativePointedConeTriangleLift c s hs k
local notation "hN" => nativePointedConeTriangleLift_projection c s hs k
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ s
local notation "hv" => nativePointedConeTriangle_initial c s hs k

/-- native 全錐と元の全三角形の同じ指定比較を、指定面上の切断族へ写す。 -/
def nativePointedTriangleFaceSectionsIso
    (H : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hH : H ≫ pointedSpaceProjection = fst Δ[2] A ≫ Dk) (hH₀ : i ≫ H = v) :
    FunctorIso (pointedTriangleFaceSections Dk N hN face)
      (pointedTriangleFaceSections Dk H hH face) :=
  relativeExtensionCurryRestrictionIso pointedSpaceProjection (fst Δ[2] A ≫ Dk) i v hv
    (stdSimplex.δ face ▷ A) (stdSimplex.δ face ≫ Dk)
    (by rw [← Category.assoc, whiskerRight_fst, Category.assoc])
    N H hN hH (nativePointedConeTriangleLift_initial c s hs k) hH₀
    (nativePointedTriangleComparisonIso c s hs k H hH hH₀)

end SerrePositivity.InfinityCategories.F2
