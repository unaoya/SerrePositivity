module
public import SerrePositivity.KST.SConstruction.ReducedPathBoundary
public import SerrePositivity.KST.SConstruction.PointedContractibility

/-! # 定数部分を潰した反復経路と可縮 Kan 模型
概要：反復経路を点つき関手として構成し、その Kan 置換の全境界充填を証明する。
方針：零段の弱可縮性により定数切断を潰す商が弱同値であることを使う。
規約：境界の標的は最内側の一つの零方向の商。使われ方：点つきの経路全空間。
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

/-- 概要：最内側の S の各段に反復実現を施した図式の入力への関手。
方針：単体的 S 自己関手の変数を反転し、反復実現を後合成する。
規約：各値は既存の iteratedSRealizationDiagram。使われ方：点つき反復経路の関手性。 -/
def iteratedSRealizationDiagramFunctor (r : ℕ) :
    StableModel.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) :=
  simplicialStableEndofunctor.flip ⋙
    (Functor.whiskeringRight _ _ _).obj (multiRealizationFunctor r)

/-- 概要：定数部分を潰して点つきにした反復経路の関手。
方針：反復した S の図式に定数経路を潰す関手を後合成する。
規約：chosen zero を使わない。使われ方：自然な点つき経路全空間。 -/
def pointedIteratedPathFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  iteratedSRealizationDiagramFunctor r ⋙ reducedPathDiagonalFunctor

/-- 概要：入力ごとの点つき反復経路実現。
方針：定数部分を潰す関手で入力を評価する。
規約：全空間はまだ Kan と仮定しない。使われ方：Kan 置換前の経路模型。 -/
def pointedIteratedPathRealization (r : ℕ) (X : StableModel.{u}) : PointedSimplicialSet.{u} :=
  (pointedIteratedPathFunctor r).obj X

/-- 概要：元の反復経路から定数部分を潰す点つき模型への商射影。
方針：一般の定数経路の商写像を適用する。
規約：底の単体集合の射。使われ方：元の経路との弱同値比較。 -/
def pointedIteratedPathQuotient (r : ℕ) (X : StableModel.{u}) :
    iteratedPathRealization r X ⟶ (pointedIteratedPathRealization r X).right :=
  pathDiagonalReductionQuotient (iteratedSRealizationDiagram r X)

/-- 概要：点つき反復経路への商写像は全 anodyne 反転関手で可逆。
方針：定数切断の源は S₀X の反復実現なので弱可縮である。
規約：商の源と標的の Kan 性は不要。使われ方：点つき経路全空間の弱可縮性。 -/
lemma pointedIteratedPathQuotient_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map (pointedIteratedPathQuotient r X)) :=
  pathDiagonalReductionQuotient_image_isIso L hL (iteratedSRealizationDiagram r X)
    (multiRealization_toPoint_localized_isIso_of_contractible r (sStableModel 0 X)
      (sConstructionZero_isContractibleKan X.carrier))

/-- 概要：定数部分を潰した点つき反復経路の底は弱可縮。
方針：元の経路の弱可縮性と商射影の弱同値を合成から打ち消す。
規約：反復回数零を含む。使われ方：Kan 置換後の可縮性。 -/
lemma pointedIteratedPath_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (toUnit (pointedIteratedPathRealization r X).right)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := pointedIteratedPathQuotient_image_isIso Q (Localization.inverts Q anodyneExtensions) r X
  have hc : IsIso (Q.map (pointedIteratedPathQuotient r X) ≫
      Q.map (toUnit (pointedIteratedPathRealization r X).right)) := by
    rw [← Q.map_comp, comp_toUnit]
    exact iteratedPathRealization_toPoint_localized_isIso r X
  exact (isIso_comp_left_iff _ _).mp hc

/-- 概要：点つき反復経路から最内側の零方向の商への境界の自然変換。
方針：一般の点つき経路境界を反復 S の図式で前合成する。
規約：標的はまだ全零方向の商ではない。使われ方：点つき境界の関手性。 -/
def pointedIteratedPathBoundaryNat (r : ℕ) : pointedIteratedPathFunctor.{u} r ⟶
    iteratedSRealizationDiagramFunctor r ⋙ reducedDiagonalFunctor :=
  Functor.whiskerLeft (iteratedSRealizationDiagramFunctor r) reducedPathDiagonalBoundaryNat

/-- 概要：点つき反復経路の入力ごとの実際の境界射。
方針：構成した自然変換の成分を取る。
規約：基点を厳密に保つ。使われ方：fiber 比較の点つき境界の一段目。 -/
def pointedIteratedPathBoundary (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathRealization r X ⟶ reducedDiagonal (iteratedSRealizationDiagram r X) :=
  (pointedIteratedPathBoundaryNat r).app X

/-- 概要：点つき反復経路の境界は商射影の前で元の境界を回収する。
方針：一般の点つき経路境界の降下の式を使う。
規約：厳密等号。使われ方：既存の境界と構造射の比較。 -/
lemma pointedIteratedPathBoundary_quotient (r : ℕ) (X : StableModel.{u}) :
    pointedIteratedPathQuotient r X ≫ (pointedIteratedPathBoundary r X).right =
      iteratedPathRealizationBoundary r X ≫
        diagonalReductionQuotient (iteratedSRealizationDiagram r X) :=
  reducedPathDiagonalBoundary_quotient (iteratedSRealizationDiagram r X)

/-- 概要：点つき反復経路の Kan 置換の関手。
方針：既存の L9 の点つき Kan 置換を後合成する。
規約：選択した零対象に依存しない。使われ方：可縮 Kan な経路全空間。 -/
def pointedIteratedPathKanFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  pointedIteratedPathFunctor r ⋙ Spectra.PointedKanReplacement.functor

/-- 概要：点つき反復経路の Kan 置換の底は Kan 複体。
方針：L9 の置換の Kan 性。
規約：全ての安定な入力。使われ方：実際の可縮 Kan 性。 -/
instance pointedIteratedPathKan_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((pointedIteratedPathKanFunctor r).obj X).right) :=
  Spectra.PointedKanReplacement.obj_kanComplex _

/-- 概要：点つき反復経路の Kan 置換は弱可縮。
方針：anodyne な置換単位と元の点つき経路の弱可縮性を合成から打ち消す。
規約：置換は L9 の実際の関手。使われ方：全境界の充填の導出。 -/
lemma pointedIteratedPathKan_toPoint_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (((pointedIteratedPathKanFunctor r).obj X).right))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let i :=
    (Spectra.PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right
  have hi : IsIso (Q.map i) := (Localization.inverts Q anodyneExtensions) i
    (Spectra.PointedKanReplacement.unit_anodyne _)
  have hc : IsIso (Q.map i ≫
      Q.map (toUnit (((pointedIteratedPathKanFunctor r).obj X).right))) := by
    rw [← Q.map_comp]
    have ht : i ≫ toUnit (((pointedIteratedPathKanFunctor r).obj X).right) =
        toUnit (pointedIteratedPathRealization r X).right := isTerminalTensorUnit.hom_ext _ _
    rw [ht]
    exact pointedIteratedPath_toPoint_localized_isIso r X
  exact (isIso_comp_left_iff _ _).mp hc

/-- 概要：点つき反復経路の Kan 模型は実際に全境界を充填する可縮 Kan 複体。
方針：点つき Kan な模型の弱可縮性を一般の Whitehead の充填へ渡す。
規約：追加の存在仮定なし。使われ方：delooping の可縮な点つき経路全空間。 -/
lemma pointedIteratedPathKan_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (((pointedIteratedPathKanFunctor r).obj X).right) :=
  pointedIsContractibleKan_of_localized_toPoint _
    (pointedIteratedPathKan_toPoint_localized_isIso r X)

/-- 概要：Kan 置換した点つき反復経路の境界の自然変換。
方針：点つき境界の自然変換を L9 の点つき Kan 置換で写す。
規約：源の各値は可縮 Kan。使われ方：homotopy fiber の Kan 模型。 -/
def pointedIteratedPathKanBoundaryNat (r : ℕ) : pointedIteratedPathKanFunctor.{u} r ⟶
    (iteratedSRealizationDiagramFunctor r ⋙ reducedDiagonalFunctor) ⋙
      Spectra.PointedKanReplacement.functor :=
  Functor.whiskerRight (pointedIteratedPathBoundaryNat r) Spectra.PointedKanReplacement.functor

/-- 概要：可縮な点つき Kan 経路全空間からの実際の境界射。
方針：Kan 置換した境界の自然変換の成分を取る。
規約：標的は最内側の零方向を潰す実現の Kan 置換。使われ方：fiber と loop の比較の入力。 -/
def pointedIteratedPathKanBoundary (r : ℕ) (X : StableModel.{u}) :
    (pointedIteratedPathKanFunctor r).obj X ⟶
      Spectra.PointedKanReplacement.obj (reducedDiagonal (iteratedSRealizationDiagram r X)) :=
  (pointedIteratedPathKanBoundaryNat r).app X

end SerrePositivity.KST.SConstruction
