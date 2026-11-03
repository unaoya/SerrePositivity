module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRestrictedPrismVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanCommonLongPath

/-!
概要：既存の左右の実 prism 制限を、同じ native 共通長辺空間へ移す。
方針：元の共通長辺の等式と実制限の底の照合を正規化へ適用する。
規約：元の普遍 prism と全三角形の長辺を保持。使われ方：既存の局所比較との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "A" => leftUnstraightening F
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => Over.Hom.left m ≫ lift (𝟙 A) (SSet.const l)
local notation "dl" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const C.leftTriangle.diagonal))
local notation "dr" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ Δ[0]) ≫
  functorParameterizedPrism (intervalMappingUncurry (SSet.const C.rightTriangle.diagonal))
local notation "q" => coherentCospanNativeLongBase F X Y Z C b
local notation "hq" => coherentCospanNativeLongBase_initial F X Y Z C b

/-- 既存の左 prism 制限の底は共通の native 長辺の底そのもの。 -/
lemma coherentCospanRestrictedPrismBase_left : prismParameterRestriction s ≫ dl = q := by
  have h := congrArg SSet.yonedaEquiv.symm
    (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)
  simp only [coherentTransformationPointTriangle, Equiv.symm_apply_apply] at h
  unfold coherentCospanNativeLongBase
  rw [h]
  exact coherentRestrictedPrism_base F X Z C.toLeft C.fromLeft C.leftTriangle b

/-- 既存の右 prism 制限も、元の共通長辺の等式で同じ底へ揃う。 -/
lemma coherentCospanRestrictedPrismBase_right : prismParameterRestriction s ≫ dr = q := by
  rw [← C.diagonal_eq]
  exact coherentCospanRestrictedPrismBase_left F X Y Z C b

/-- 元の左の普遍 prism の実頂点を共通空間へ移す。 -/
def coherentCospanRestrictedUniversalLeft :=
  coherentRestrictedPrismUniversalVertex F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 元の右の普遍 prism の実頂点を同じ共通空間へ移す。 -/
def coherentCospanRestrictedUniversalRight :=
  coherentRestrictedPrismUniversalVertex F Y Z C.toRight C.fromRight C.rightTriangle b q hq
    (coherentCospanRestrictedPrismBase_right F X Y Z C b)

/-- 元の左三角形の長辺の実頂点を共通空間へ移す。 -/
def coherentCospanRestrictedLongLeft :=
  coherentRestrictedPrismLongVertex F X Z C.toLeft C.fromLeft C.leftTriangle b q hq
    (coherentCospanRestrictedPrismBase_left F X Y Z C b)

/-- 元の右三角形の長辺の実頂点を同じ共通空間へ移す。 -/
def coherentCospanRestrictedLongRight :=
  coherentRestrictedPrismLongVertex F Y Z C.toRight C.fromRight C.rightTriangle b q hq
    (coherentCospanRestrictedPrismBase_right F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
