module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeSquareCells
public import SerrePositivity.KST.SConstruction.TriangleCylinderPasting
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCorrectionProjection

/-! # 元の全三角形と全交換セルを保持する実比較複体
概要：元の第二面に全二次元補正列を貼り、三角形・共有面・全セルを同時に保持する。
方針：元の実三角形と補正列の pushout を、共通三精密化上で構成する。
規約：元の全二単体と交換正方形の全体・順序を厳密に回収する。零段も含む。
使われ方：全段の raw 比較入力への実二次元貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の三角形と元の全二次元補正セルを貼った実複体。 -/
def monicKPrismNativePastingDomain (n : ℕ) : SSet.{u} :=
  triangleCylinderPastingDomain (monicKPrismCompositionNativeTriangle n F f g)
    (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 元の三角形全体の、実複体への包含。 -/
def monicKPrismNativePastingTriangle (n : ℕ) :
    nerve (CompositionStringParameters f g) ⊗ (Δ[2] : SSet.{u}) ⟶
      monicKPrismNativePastingDomain F f g n :=
  triangleCylinderPastingTriangle _ (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 貼り合わせ全体から、元の単射源の suspension Hom への実写像。 -/
def monicKPrismNativePastingMap (n : ℕ) : monicKPrismNativePastingDomain F f g n ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kOmegaSpectrum (F.obj x)).level n).space)
      ((kKanSequence (F.obj z)).level (n + 1)).space).right :=
  triangleCylinderPastingMap _ (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 複体内の、元の交換正方形全体の包含を順に保持する。 -/
def monicKPrismNativePastingCells (n : ℕ) :=
  triangleCylinderPastingCells _ (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 全セルの複体内での共有面と、入口・出口の厳密な歩道。 -/
def monicKPrismNativePastingWalk (n : ℕ) :=
  triangleCylinderPastingWalk _ (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 補正後の同じ適合円柱を表す、複体内の出口。 -/
def monicKPrismNativePastingTarget (n : ℕ) :
    nerve (CompositionStringParameters f g) ⊗ (Δ[1] : SSet.{u}) ⟶
      monicKPrismNativePastingDomain F f g n :=
  (familyChainPasting (monicKPrismNativeSecondCompatibilityTransport F f g n)).target ≫
    triangleCylinderPastingStrip _ (monicKPrismNativeSecondCompatibilityTransport F f g n)

/-- 元の全比較三角形を厳密に回収する。 -/
lemma monicKPrismNativePastingMap_triangle (n : ℕ) :
    monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n =
      monicKPrismCompositionNativeTriangle n F f g :=
  triangleCylinderPastingMap_triangle _ _

/-- 出口は補正済みの同じ後続適合円柱の全時刻を回収する。 -/
lemma monicKPrismNativePastingMap_target (n : ℕ) :
    monicKPrismNativePastingTarget F f g n ≫ monicKPrismNativePastingMap F f g n =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeSecondCompatibility F f g n := by
  rw [monicKPrismNativePastingTarget, Category.assoc]
  exact triangleCylinderPastingMap_target _ _

/-- 元の全交換セルと順序を、元の正方形の二時刻の交換として厳密に回収する。 -/
lemma monicKPrismNativePastingMap_cells (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (· ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompatibilityInterchangeSquares F f g n).map (fun q =>
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫
          familySquareClockSwap
            (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g)) ≫ q) :=
  (triangleCylinderPastingMap_cells _ _).trans
    (monicKPrismNativeSecondCompatibilityTransport_square_cells F f g n)

/-- 元の第一面の全区間は、同じ保存済み第一適合円柱の引き戻し。 -/
lemma monicKPrismNativePastingMap_first (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeFirstCompatibility F f g n := by
  rw [monicKPrismNativePastingMap_triangle]
  exact monicKPrismCompositionNativeTriangle_first_trace n F f g

/-- 元の合成面の全区間も、同じ合成射の raw 適合円柱。 -/
lemma monicKPrismNativePastingMap_composite (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h := by
  rw [monicKPrismNativePastingMap_triangle]
  exact monicKPrismCompositionNativeTriangle_composite_trace n F f g

/-- 零段の複体には補正セルがなく、元の全三角形だけを保持する。 -/
lemma monicKPrismNativePastingMap_zero_cells :
    (monicKPrismNativePastingCells F f g 0).map (· ≫ monicKPrismNativePastingMap F f g 0) = [] :=
  (triangleCylinderPastingMap_cells _ _).trans
    (monicKPrismNativeSecondCompatibilityTransport_zero_trace F f g)

/-- 零段には実際に円柱セルの包含自体がなく、三角形だけが残る。 -/
lemma monicKPrismNativePasting_zero_cells : monicKPrismNativePastingCells F f g 0 = [] :=
  List.map_eq_nil_iff.mp (monicKPrismNativePastingMap_zero_cells F f g)

end SerrePositivity.KST.SConstruction
