module
public import SerrePositivity.KST.SConstruction.TracedBFTripleInterchangeCells
public import SerrePositivity.InfinityCategories.Kan.CartesianInterchangeDiamond

/-! # 元の前二射 BF 比較と最終射補正の実交換三角形対
概要：元の全補正辺と BF 比較辺の段評価から、二順序の実交換三角形対を構成する。
方針：元の同じ二辺の退化三角形の直積を、同じ豊穣合成で写す。
規約：両全二単体・共通対角辺を保持し、Kan 充填を使わない。
使われ方：三入力の左右辺路で BF 比較と最後の raw 補正を交換する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 最後の全補正を先に動かす実経路の下辺。 -/
def monicKTracedTripleInterchangeFirstLower (n : ℕ) :=
  cartesianInterchangeFirstLower (monicKTracedUnaryCorrectionPointEdge F h n)
    (monicKTracedCompositionBFLevelEdge F f g n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 最後の全補正を先に動かす実経路の上辺。 -/
def monicKTracedTripleInterchangeFirstUpper (n : ℕ) :=
  cartesianInterchangeFirstUpper (monicKTracedUnaryCorrectionPointEdge F h n)
    (monicKTracedCompositionBFLevelEdge F f g n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 前二射の BF 比較を先に動かす実経路の下辺。 -/
def monicKTracedTripleInterchangeSecondLower (n : ℕ) :=
  cartesianInterchangeSecondLower (monicKTracedUnaryCorrectionPointEdge F h n)
    (monicKTracedCompositionBFLevelEdge F f g n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 前二射の BF 比較を先に動かす実経路の上辺。 -/
def monicKTracedTripleInterchangeSecondUpper (n : ℕ) :=
  cartesianInterchangeSecondUpper (monicKTracedUnaryCorrectionPointEdge F h n)
    (monicKTracedCompositionBFLevelEdge F f g n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 元の同じ全補正辺・BF 段比較辺を保持する、実交換三角形対。 -/
def monicKTracedTripleInterchangeDiamond (n : ℕ) :=
  cartesianInterchangeDiamond (monicKTracedUnaryCorrectionPointEdge F h n)
    (monicKTracedCompositionBFLevelEdge F f g n)
    (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)

/-- 第一全二単体は元の同じ二辺の下三角形の像そのもの。 -/
lemma monicKTracedTripleInterchangeDiamond_first (n : ℕ) :
    (monicKTracedTripleInterchangeDiamond F f g h n).first.simplex =
      ((cartesianEdgeLowerTriangle (monicKTracedUnaryCorrectionPointEdge F h n)
        (monicKTracedCompositionBFLevelEdge F f g n)).map
          (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)).simplex := rfl

/-- 第二全二単体も元の同じ二辺の上三角形の像そのもの。 -/
lemma monicKTracedTripleInterchangeDiamond_second (n : ℕ) :
    (monicKTracedTripleInterchangeDiamond F f g h n).second.simplex =
      ((cartesianEdgeUpperTriangle (monicKTracedUnaryCorrectionPointEdge F h n)
        (monicKTracedCompositionBFLevelEdge F f g n)).map
          (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)).simplex := rfl

/-- 共通対角辺も元の同じ二つの全辺を同時に辿った像そのもの。 -/
lemma monicKTracedTripleInterchangeDiamond_diagonal (n : ℕ) :
    (monicKTracedTripleInterchangeDiamond F f g h n).diagonal.edge =
      ((cartesianEdgePair (monicKTracedUnaryCorrectionPointEdge F h n)
        (monicKTracedCompositionBFLevelEdge F f g n)).map
          (kStageRawReverseComposition (F.obj w) (F.obj y) (F.obj z) n)).edge := rfl

/-- 元の二実三角形から、二順序の同じ合成を回収する。 -/
lemma monicKTracedTripleInterchangeDiamond_comp (n : ℕ) :
    SSet.HomotopyCategory.homMk (monicKTracedTripleInterchangeFirstLower F f g h n) ≫
        SSet.HomotopyCategory.homMk (monicKTracedTripleInterchangeFirstUpper F f g h n) =
      SSet.HomotopyCategory.homMk (monicKTracedTripleInterchangeSecondLower F f g h n) ≫
        SSet.HomotopyCategory.homMk (monicKTracedTripleInterchangeSecondUpper F f g h n) :=
  cartesianInterchangeDiamond_comp _ _ _

end SerrePositivity.KST.SConstruction
