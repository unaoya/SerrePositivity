module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCorrectionChains

/-! # 共通三精密化上の合成補正の全射影 trace
概要：補正の全射影を、元の三角形の第一面・交換正方形・後続適合円柱・前段へ分解する。
方針：保存済みの射影式を全区間ごと引き戻し、先頭を同じ元の第一面へ移す。
規約：全区間の順序と数を保持し、第二面の二次元補正を省略しない。
使われ方：全段の実比較入力と境界の貼り合わせ。
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

/-- 全補正の射影は、元の第一面から始まる同じ全区間の分解を厳密に保持する。 -/
lemma monicKPrismNativeCompositeCorrectionChain_projection_trace (n : ℕ) :
    (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g (n + 1))).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
          monicKPrismCompositionNativeTriangle n F f g) ::
        ((monicKPrismCompatibilityInterchangeSquares F f g n).map (fun q =>
            (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ SSet.ι₀ ≫ q) ++
          ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
            monicKPrismCompositeSecondCompatibility F f g n) ::
          (monicKPrismCompositeSecondTrace F f g n).map (fun h =>
            (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ h ≫
              RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) := by
  rw [monicKPrismCompositionNativeTriangle_first_trace,
    monicKPrismNativeCompositeCorrectionChain_trace]
  calc
    _ = ((familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g
        (n + 1))).map (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space)).map
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
      simp only [List.map_map, Function.comp_def, Category.assoc]
      rfl
    _ = _ := by
      rw [monicKPrismTracedCompositeCorrectionChain_projection_trace]
      simp only [List.map_map, Function.comp_def, List.map_cons, List.map_append]

end SerrePositivity.KST.SConstruction
