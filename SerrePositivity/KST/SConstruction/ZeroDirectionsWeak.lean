module
public import SerrePositivity.KST.SConstruction.ZeroDirections
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 零方向を固定した実現の弱可縮性
概要：一つ以上の零方向を固定した反復実現から一点への射は anodyne 局所化で可逆。
方針：各段の可縮 Kan 性と HA の各行の同値を対角へ移す定理を使う。
規約：対角自体が可縮 Kan とは主張しない。使われ方：境界の各交差の collapse。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：零方向の図式から一点の定値図式への自然変換。
方針：各段で終対象への一意な射を使う。
規約：内部の単体方向も保持する。使われ方：対角の比較。 -/
def zeroDirectionsDiagramToPoint {r : ℕ} (s : Finset (Fin r)) (X : StableModel.{u}) :
    zeroDirectionsDiagram s X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (𝟙_ SSet.{u}) where
  app _d := toUnit _
  naturality {_d _e} _f := isTerminalTensorUnit.hom_ext _ _

/-- 概要：非空の零方向の実現は anodyne 局所化で一点と同値。
方針：各行の可縮 Kan 複体からの射の可逆性を対角へ移す。
規約：モデル構造を仮定しない。使われ方：各境界交差の弱可縮性。 -/
lemma zeroDirectionsRealization_toPoint_localized_isIso {r : ℕ} (s : Finset (Fin r))
    (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X)))) := by
  have hi (d : SimplexCategoryᵒᵖ) :
      IsIso (AnodyneHomotopy.anodyneQ.map ((zeroDirectionsDiagramToPoint s X).app d)) := by
    have := trivialKanFibration_toUnit_of_contractible (zeroDirectionsDiagram_isContractibleKan s hs X d)
    exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
        (toUnit ((zeroDirectionsDiagram s X).obj d))
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map (zeroDirectionsDiagramToPoint s X) hi

/-- 概要：非空の零方向の実現から一点への射は全 anodyne 反転関手で可逆。
方針：anodyne 局所化から任意の反転関手へ比較を移す。
規約：値域は任意の圏。使われ方：境界の合併と π_* の比較。 -/
lemma zeroDirectionsRealization_toPoint_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) {r : ℕ}
    (s : Finset (Fin r)) (hs : s.Nonempty) (X : StableModel.{u}) :
    IsIso (L.map (toUnit (simplicialDiagonalFunctor.obj (zeroDirectionsDiagram s X)))) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _
    (zeroDirectionsRealization_toPoint_localized_isIso s hs X)

end SerrePositivity.KST.SConstruction
