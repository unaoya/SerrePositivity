module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativePreviousTrace

/-! # 同じ実貼り合わせ複体の両側にある全 raw trace
概要：次段補正の全射影と、元の合成適合辺・前段補正の全体を同じ実複体の両側に表示する。
方針：全セルの零・一境界と出口、前段の二半分の保存式を合成する。
規約：共通末尾を含めた全区間の数と順序を保存する。
使われ方：全段の実 raw 比較入力の境界として用いる二つの全 trace。
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

/-- 一境界と共通の後半末尾は、前段の補正全列の同じ構造射による像。 -/
lemma monicKPrismNativePasting_previous_full_trace (n : ℕ) :
    (monicKPrismNativePastingCells F f g n).map (fun q =>
        (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
          q ≫ monicKPrismNativePastingMap F f g n) ++
      (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
        (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
          RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) =
      (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g n)).map
        (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativePastingMap_cells_one_previous_trace,
    monicKPrismNativeCompositeCorrectionChain_trace,
    monicKPrismTracedCompositeCorrectionChain_trace]
  simp only [List.map_append, List.map_map, Function.comp_def, Category.assoc]
  rfl

/-- 次段の射影全 trace は、元の第一面・全零境界・出口・共通末尾からなる。 -/
lemma monicKPrismNativePasting_projected_full_trace (n : ℕ) :
    (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g (n + 1))).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
          monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n) ::
        ((monicKPrismNativePastingCells F f g n).map (fun q =>
            (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
              q ≫ monicKPrismNativePastingMap F f g n) ++
          (monicKPrismNativePastingTarget F f g n ≫ monicKPrismNativePastingMap F f g n) ::
            (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
              (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
                RawSpectrumMapping.step (kOmegaSpectrum (F.obj x))
                  (kKanSequence (F.obj z)) n)) := by
  rw [monicKPrismNativePastingMap_triangle, monicKPrismNativePastingMap_target,
    monicKPrismNativePastingMap_cells_zero_faces]
  exact monicKPrismNativeCompositeCorrectionChain_projection_trace F f g n

/-- もう一方の全 trace は、元の合成適合円柱と前段の全補正の構造射の像。 -/
lemma monicKPrismNativePasting_original_full_trace (n : ℕ) :
    ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativePastingTriangle F f g n ≫ monicKPrismNativePastingMap F f g n) ::
      ((monicKPrismNativePastingCells F f g n).map (fun q =>
          (SSet.ι₁ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
            q ≫ monicKPrismNativePastingMap F f g n) ++
        (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
          (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
            RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) =
      ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
          (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h) ::
        (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g n)).map
          (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativePastingMap_composite, monicKPrismNativePasting_previous_full_trace]

end SerrePositivity.KST.SConstruction
