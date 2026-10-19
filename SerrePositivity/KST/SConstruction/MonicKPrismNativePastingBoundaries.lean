module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativePasting

/-! # 貼り合わせた全交換セルの両側の元の全 trace
概要：全セルの二つの横境界を、元の補正全区間の二種類の実合成へ照合する。
方針：二時刻交換の四面の式と、元の交換正方形列の両面の等号を使う。
規約：零面だけでなく一面も全区間・順序を保持し、共有面は実歩道に保持する。
使われ方：前段の全補正 trace と次段の射影全 trace の実二次元比較。
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

/-- 貼り合わせた全セルの 零横面は、元の同じ交換正方形列の 零面。 -/
lemma monicKPrismNativePastingMap_cells_zero_faces (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
      (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        q ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompatibilityInterchangeSquares F f g n).map (fun q =>
        (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ SSet.ι₀ ≫ q) := by
  calc
    _ = ((monicKPrismNativePastingCells F f g n).map
        (· ≫ monicKPrismNativePastingMap F f g n)).map
        ((SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by
      rw [monicKPrismNativePastingMap_cells]
      simp only [List.map_map, Function.comp_def,
        familySquareClockSwap_first_zero_restrict_assoc]

/-- 貼り合わせた全セルの 零境界は、元の全補正区間の同じ実前後合成。 -/
lemma monicKPrismNativePastingMap_cells_zero_trace (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
      (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        q ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompatibilityInterchangeTrace F f g n
        ((kKanSequence (F.obj y)).sigma n ≫ kKanSequenceLevelMap (F.map g) (n + 1))).map
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativePastingMap_cells_zero_faces]
  have h := congrArg
    (List.map ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·))
    (monicKPrismCompatibilityInterchangeSquares_second_zero F f g n)
  simpa only [List.map_map, Function.comp_def, Category.assoc] using h

/-- 貼り合わせた全セルの 一横面は、元の同じ交換正方形列の 一面。 -/
lemma monicKPrismNativePastingMap_cells_one_faces (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
      (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        q ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompatibilityInterchangeSquares F f g n).map (fun q =>
        (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ SSet.ι₁ ≫ q) := by
  calc
    _ = ((monicKPrismNativePastingCells F f g n).map
        (· ≫ monicKPrismNativePastingMap F f g n)).map
        ((SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by
      rw [monicKPrismNativePastingMap_cells]
      simp only [List.map_map, Function.comp_def,
        familySquareClockSwap_first_one_restrict_assoc]

/-- 貼り合わせた全セルの 一境界は、元の全補正区間の同じ実前後合成。 -/
lemma monicKPrismNativePastingMap_cells_one_trace (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
      (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        q ≫ monicKPrismNativePastingMap F f g n) =
      (monicKPrismCompatibilityInterchangeTrace F f g n
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map g) n ≫
          (kKanSequence (F.obj z)).sigma n)).map
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativePastingMap_cells_one_faces]
  have h := congrArg
    (List.map ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·))
    (monicKPrismCompatibilityInterchangeSquares_second_one F f g n)
  simpa only [List.map_map, Function.comp_def, Category.assoc] using h

end SerrePositivity.KST.SConstruction
