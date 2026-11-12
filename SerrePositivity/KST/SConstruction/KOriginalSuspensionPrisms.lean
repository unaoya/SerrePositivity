module
public import SerrePositivity.KST.SConstruction.KOriginalSuspensionDiagrams

/-! # 元の K の全段・全合成列の suspension prism
概要：元の零段を保つ K の列の全段を、全合成列の整合的な prism として与える。
方針：全段の全入力円柱を同じ Yoneda 制限で写す。
規約：全ての縦辺は元の Kan 列の固定構造射。BF の厳密化は後続工程。
使われ方：零段を含む指定四辺と全合成列の高次の整合性を厳密化へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kOriginalSuspensionPrisms_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全体円柱の合成列への制限。一次元では自然性 square。 -/
def kKanOriginalSuspensionPrism {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    (Δ[n] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SimplicialNerve PointedSimplicialSet.{u} :=
  homotopySimplexPrism (kKanOriginalSuspensionHomotopy F r) (ULift.up s)

/-- prism の始点は、元の各段の通常の図式を suspension したもの。 -/
lemma kKanOriginalSuspensionPrism_zero {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    SSet.ι₀ ≫ kKanOriginalSuspensionPrism r F s =
      SSet.yonedaEquiv.symm (ULift.up s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor r) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor := by
  have hs : kKanCoherentLevelDiagram F r ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor r) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor := by
    rw [← Category.assoc, kKanCoherentLevelDiagram_inclusion]
  have h := homotopySimplexPrism_zero (kKanOriginalSuspensionHomotopy F r)
    (ULift.up s)
  conv at h => rhs; rw [hs]
  exact h

/-- prism の終点は、元の次段の通常の図式そのもの。 -/
lemma kKanOriginalSuspensionPrism_one {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    SSet.ι₁ ≫ kKanOriginalSuspensionPrism r F s =
      SSet.yonedaEquiv.symm (ULift.up s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor (r + 1)) := by
  have h := homotopySimplexPrism_one (kKanOriginalSuspensionHomotopy F r)
    (ULift.up s)
  conv at h => rhs; rw [kKanCoherentLevelDiagram_inclusion F (r + 1)]
  exact h

/-- 全合成列の面・退化は、同じ prism の制限として厳密に可換。 -/
lemma kKanOriginalSuspensionPrism_naturality {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : (nerve I) _⦋n⦌) :
    (SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u + 1})) ≫
      kKanOriginalSuspensionPrism r F s =
        kKanOriginalSuspensionPrism r F ((nerve I).map θ.op s) :=
  homotopySimplexPrism_naturality (kKanOriginalSuspensionHomotopy F r) θ (ULift.up s)

/-- 全合成列の各頂点で、元の固定 suspension 構造射の辺を厳密に回収する。 -/
lemma kKanOriginalSuspensionPrism_vertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌)
    (a : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
    lift (SSet.const a) (𝟙 (Δ[1] : SSet.{u + 1})) ≫
      kKanOriginalSuspensionPrism r F s =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj (s.obj (a 0)))).sigma r)).edge := by
  have ha : (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve I)).app (Opposite.op ⦋0⦌) a =
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj (a 0))) := by
    apply congrArg ULift.up
    exact ComposableArrows.ext₀ rfl
  have h := homotopySimplexPrism_vertex (kKanOriginalSuspensionHomotopy F r)
    (ULift.up s) a
  rw [ha, kKanOriginalSuspensionHomotopy_vertex_edge] at h
  exact h

/-- 正の段の prism は、同じ元の反復 S の prism そのもの。 -/
lemma kKanOriginalSuspensionPrism_succ {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    kKanOriginalSuspensionPrism (r + 1) F s =
      boundaryAssemblyOriginalSuspensionPrism r F s := rfl

/-- 零段の prism は、元の余単位の strict な変換の同じ円柱の制限。 -/
lemma kKanOriginalSuspensionPrism_zero_stage {I : Type u} [SmallCategory I]
    (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    kKanOriginalSuspensionPrism 0 F s =
      homotopySimplexPrism
        (StrictDiagramTransformation.homotopy (kKanZeroSuspensionTransformation F))
        (ULift.up s) := rfl

end SerrePositivity.KST.SConstruction
