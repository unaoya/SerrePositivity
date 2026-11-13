module
public import SerrePositivity.KST.SConstruction.SimplicialPathContraction
public import SerrePositivity.KST.SConstruction.ReductionEquivalence
public import SerrePositivity.KST.SConstruction.CoreSimplicial
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # S の経路実現の弱可縮性
概要：S の core の経路実現は anodyne 局所化で一点と同値。
方針：経路の対角の変形収縮と S₀ の可縮 Kan 性を使う。
規約：経路実現を Kan と仮定しない。使われ方：delooping の経路全空間。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：経路実現の零段への射影は全 anodyne 反転関手で可逆。
方針：実際の切断と変形収縮のホモトピーを関手で写す。
規約：図式の Kan 性は不要。使われ方：経路実現の弱可縮性。 -/
lemma simplicialPathDiagonalProjection_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u}) : IsIso (L.map (simplicialPathDiagonalProjection X)) := by
  let e : L.obj (simplicialDiagonalFunctor.obj (simplicialPath X)) ≅
      L.obj (X.obj (Opposite.op ⦋0⦌)) := {
    hom := L.map (simplicialPathDiagonalProjection X)
    inv := L.map (simplicialPathDiagonalSection X)
    hom_inv_id := by
      rw [← L.map_comp, AnodyneHomotopy.map_homotopy_eq L hL
        (simplicialPathDiagonalContraction X), L.map_id]
    inv_hom_id := by rw [← L.map_comp, simplicialPathDiagonalSection_projection, L.map_id] }
  exact e.isIso_hom

/-- 概要：零段が可縮 Kan の経路実現から一点への射は全 anodyne 反転関手で可逆。
方針：零段への射影と、零段から一点への自明ファイブレーションを合成する。
規約：経路実現の Kan 性は不要。使われ方：S の経路空間の弱可縮性。 -/
lemma simplicialPathDiagonal_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (X : SimplicialObject SSet.{u}) (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (X.obj (Opposite.op ⦋0⦌))) :
    IsIso (L.map (toUnit (simplicialDiagonalFunctor.obj (simplicialPath X)))) := by
  have := simplicialPathDiagonalProjection_image_isIso L hL X
  have := trivialKanFibration_toUnit_of_contractible hX
  have := map_isIso_of_trivialKanFibration L hL (toUnit (X.obj (Opposite.op ⦋0⦌)))
  have he : simplicialPathDiagonalProjection X ≫ toUnit (X.obj (Opposite.op ⦋0⦌)) =
      toUnit (simplicialDiagonalFunctor.obj (simplicialPath X)) := isTerminalTensorUnit.hom_ext _ _
  rw [← he, L.map_comp]
  infer_instance

/-- 概要：S の core の先頭頂点を残す経路構成の対角実現。
方針：単体的 core S に経路構成を施して対角を取る。
規約：全 gapped 図式を保持。使われ方：delooping の経路全空間。 -/
def sPathRealization (C : SSet.{u}) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (simplicialPath (simplicialCoreSConstruction C))

/-- 概要：S の経路実現から零図式の core への実際の射影。
方針：一般の経路実現の augmentation を使う。
規約：先頭頂点への制限。使われ方：零段へのホモトピー同値。 -/
def sPathRealizationProjection (C : SSet.{u}) : sPathRealization C ⟶ coreSConstruction 0 C :=
  simplicialPathDiagonalProjection (simplicialCoreSConstruction C)

/-- 概要：零対象を持つ quasicategory の S の経路実現は弱可縮。
方針：S₀ の core の可縮 Kan 性と一般の経路実現の比較を使う。
規約：追加の安定性は不要。使われ方：S の delooping の経路全空間の比較。 -/
lemma sPathRealization_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L)
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    IsIso (L.map (toUnit (sPathRealization C))) :=
  simplicialPathDiagonal_toPoint_image_isIso L hL (simplicialCoreSConstruction C)
    (coreSConstructionZero_isContractibleKan C)

end SerrePositivity.KST.SConstruction
