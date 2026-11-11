module
public import SerrePositivity.KST.SConstruction.MultiRealization
public import SerrePositivity.KST.SConstruction.ReductionEquivalence
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.KST.SConstruction.KSpace

/-! # 選択なしの基点を持つ反復実現と K 空間
概要：反復 core S の同時零段全体を潰して、点つき実現・Kan 置換・Ω を関手として作る。
方針：一般の reduced diagonal を多単体的反復の対角図式に適用する。
規約：個々の零方向全体を同時に潰す fat wedge は別工程。使われ方：自然な K の基点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：全 S 方向を対角に制限した単体的単体集合を入力について関手化する。
方針：多単体的 core の関手を添字の対角で前合成する。
規約：内部の単体方向はまだ実現しない。使われ方：零段を潰す実現の入力。 -/
def multiDiagonalDiagramFunctor (r : ℕ) : StableModel.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) :=
  multiCoreSConstructionFunctor r ⋙ (Functor.whiskeringLeft _ _ _).obj (multiIndexDiagonal r)

/-- 概要：正の反復の同時零段は可縮 Kan 複体。
方針：任意の一つの零方向の可縮性を適用する。
規約：反復回数は r+1。使われ方：商写像の弱同値性。 -/
lemma multiDiagonalDiagram_zero_isContractibleKan (r : ℕ) (X : StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (((multiDiagonalDiagramFunctor (r + 1)).obj X).obj (Opposite.op ⦋0⦌)) :=
  multiCoreSConstruction_isContractibleKan_of_zero_coordinate (r + 1) X
    (fun _ => Opposite.op ⦋0⦌) 0 rfl

/-- 概要：同時零段全体を潰す、選択なしの点つき反復実現の関手。
方針：多単体的 core の対角図式に reduced diagonal を適用する。
規約：r+1 重の S を使う。使われ方：反復実現の自然な基点。 -/
def reducedMultiRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  multiDiagonalDiagramFunctor (r + 1) ⋙ reducedDiagonalFunctor

/-- 概要：通常の反復実現から同時零段を潰す実現への自然変換。
方針：零段を潰す商写像の自然変換で前合成する。
規約：入力の射は chosen zero を保つ必要がない。使われ方：実現模型の自然な比較。 -/
def multiRealizationReductionNat (r : ℕ) : multiRealizationFunctor (r + 1) ⟶
    reducedMultiRealizationFunctor r ⋙ PointedSimplicialSet.forget :=
  Functor.whiskerLeft (multiDiagonalDiagramFunctor (r + 1)) diagonalReductionNat

/-- 概要：反復実現の商写像は anodyne を反転する全関手で可逆。
方針：同時零段の可縮性と商写像の pushout cube 比較を使う。
規約：対角や商の Kan 性は不要。使われ方：自然な実現模型の同値比較。 -/
lemma multiRealizationReduction_image_isIso {D : Type v} [Category.{w} D]
    (L : SSet.{u} ⥤ D) (hL : anodyneExtensions.IsInvertedBy L) (r : ℕ) (X : StableModel.{u}) :
    IsIso (L.map ((multiRealizationReductionNat r).app X)) :=
  diagonalReductionQuotient_image_isIso L hL ((multiDiagonalDiagramFunctor (r + 1)).obj X)
    (multiDiagonalDiagram_zero_isContractibleKan r X)

/-- 概要：選択なしの点つき反復実現を関手的に Kan 置換する。
方針：L9 の点つき Kan 置換関手との合成。
規約：元の実現の Kan 性を仮定しない。使われ方：連結スペクトルの fibrant な空間。 -/
def reducedMultiKanRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  reducedMultiRealizationFunctor r ⋙ Spectra.PointedKanReplacement.functor

/-- 概要：点つき反復実現の置換の各値は Kan 複体。
方針：L9 の点つき置換の instance を使う。
規約：全ての安定な入力に適用する。使われ方：Ω と π_*。 -/
instance reducedMultiKanRealization_kanComplex (r : ℕ) (X : StableModel.{u}) :
    KanComplex (((reducedMultiKanRealizationFunctor r).obj X).right) :=
  Spectra.PointedKanReplacement.obj_kanComplex _

/-- 概要：選択なしの点つき一重 S 実現の Ω を取る K 空間の関手。
方針：L9 の Kan 置換と円からの点つき内部 Hom を合成する。
規約：旧 K 空間との比較は別の宣言で示す。使われ方：dg 適用に必要な自然性。 -/
def reducedKSpaceFunctor : StableModel.{u} ⥤ PointedSimplicialSet.{u} :=
  reducedMultiKanRealizationFunctor 0 ⋙
    PointedObject.basedHomFunctor (C := SSet.{u}) PointedSimplicialSet.circle.{u}

/-- 概要：選択なしの K 空間の各値は Kan 複体。
方針：置換の Kan 性と L9 の loop の Kan 性を使う。
規約：Ω は L9 の既存の模型。使われ方：K のホモトピー群。 -/
instance reducedKSpaceFunctor_kanComplex (X : StableModel.{u}) :
    KanComplex ((reducedKSpaceFunctor.obj X).right) :=
  Spectra.loopSpace_kanComplex ((reducedMultiKanRealizationFunctor 0).obj X)

end SerrePositivity.KST.SConstruction
