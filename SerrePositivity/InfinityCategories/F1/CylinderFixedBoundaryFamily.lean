module

public import SerrePositivity.InfinityCategories.F1.IntervalBoundaryFamilyData
public import SerrePositivity.InfinityCategories.F1.RelativeBoundaryFixedFamilyFiber

/-!
概要：両端写像を固定した実際の円柱の区間族と、四角形の厳密な境界 fiber の同型。
方針：円柱の二端点の射影を計算して一般の区間データと fiber 同型を特殊化する。
規約：区間内部の分類図式は固定しない。
使われ方：円柱の両端制限の可縮性を実際の族の lift 空間へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：円柱の共通境界の左成分は区間の零端へ写る。
方針：共通境界の左包含と円柱の始点の公式。
規約：貼り付け射 f は任意。
使われ方：実際の境界固定区間データの左条件。 -/
lemma transportCylinderBoundary_zero {K J : SSet.{u}} (f : K ⟶ J) :
    (joinEndpointInl K J ≫ transportCylinderEndpointInclusion f) ≫
      mappingCylinderIntervalProjection f = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change cylinderSquareSourceInclusion f ≫ mappingCylinderIntervalProjection f = _
  exact cylinderSquareSourceInclusion_projection f

/-- 概要：円柱の共通境界の右成分は区間の一端へ写る。
方針：共通境界の右包含と円柱の終点の公式。
規約：貼り付け射 f は任意。
使われ方：実際の境界固定区間データの右条件。 -/
lemma transportCylinderBoundary_one {K J : SSet.{u}} (f : K ⟶ J) :
    (joinEndpointInr K J ≫ transportCylinderEndpointInclusion f) ≫
      mappingCylinderIntervalProjection f = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change pushout.inr (prismEndpoint 1 K) f ≫ mappingCylinderIntervalProjection f = _
  exact mappingCylinderIntervalProjection_inr f

/-- 概要：円柱の境界と底のための相対内部 Hom。
方針：共通の二端点図式の包含に対する標準相対内部 Hom を取る。
規約：定義に境界包含の単射性や係数の充填性は不要。
使われ方：両端写像を固定した全円柱 lift 空間。 -/
def cylinderBoundaryRelativeHom {K J : SSet.{u + 1}} (f : K ⟶ J) :
    internalHom.PullbackObjObj (transportCylinderEndpointInclusion f) pointedSpaceProjection :=
  Functor.PullbackObjObj.ofHasPullback internalHom _ _

/-- 概要：円柱上の両端固定区間の実際の境界データ。
方針：固定した両端の写像と普遍区間を一般のデータ構成へ渡す。
規約：両端写像に同値性はまだ要求しない。
使われ方：円柱と区間全空間の族の比較を具体化する。 -/
def cylinderFixedBoundaryFamilyData {K J : SSet.{u + 1}} (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    intervalMappingSpace s t ⟶ (cylinderBoundaryRelativeHom f).pt :=
  intervalBoundaryFamilyData (mappingCylinderIntervalProjection f)
    (transportCylinderEndpointInclusion f)
    (transportCylinderBoundary_zero f) (transportCylinderBoundary_one f)
    (cylinderBoundaryRelativeHom f) g₀ g₁

/-- 概要：両端写像を固定し分類区間全体を動かす円柱上の全 lift 空間。
方針：実際のデータに沿って相対内部 Hom を引き戻す。
規約：全ての高次 lift と内部の分類区間を含む。
使われ方：円柱の可縮な両端 fiber の族としての表示。 -/
def cylinderFixedBoundaryFamilySpace {K J : SSet.{u + 1}} (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) : SSet.{u + 1} :=
  relativeBoundaryFamilySpace (cylinderBoundaryRelativeHom f)
    (cylinderFixedBoundaryFamilyData f g₀ g₁)

/-- 概要：実際の円柱の境界固定 lift 空間は四角形空間の厳密な境界 fiber と同型。
方針：動く分類図式と定値な境界の一般の fiber 同型を特殊化する。
規約：区間の内部の分類図式は自由に動く。
使われ方：実際の両端制限の可縮な fiber との同定。 -/
def cylinderFixedBoundaryFamilyFiberIso {K J : SSet.{u + 1}} (f : K ⟶ J)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    cylinderFixedBoundaryFamilySpace f g₀ g₁ ≅
      vertexFiber (cylinderFixedEndpointSquarePointed f s t ≫
        (pre (transportCylinderEndpointInclusion f)).app _)
          (functorVertex (intervalBoundaryPointedMap g₀ g₁)) :=
  relativeBoundaryFixedFamilyFiberIso (transportCylinderEndpointInclusion f) pointedSpaceProjection
    (cylinderBoundaryRelativeHom f) (intervalBoundaryPointedMap g₀ g₁)
    (cylinderIntervalDiagramι s t ≫ (pre (mappingCylinderIntervalProjection f)).app _)
    (intervalBoundaryFamily_compatibility _ _ (transportCylinderBoundary_zero f)
      (transportCylinderBoundary_one f) g₀ g₁)

end SerrePositivity.InfinityCategories
