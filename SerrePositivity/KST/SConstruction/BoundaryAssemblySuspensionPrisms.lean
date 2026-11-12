module
public import SerrePositivity.KST.SConstruction.CoherentHomotopyPrisms
public import SerrePositivity.KST.SConstruction.PointedSuspensionCoherentDiagram

/-! # 固定 suspension 構造射の全合成列に対する prism
概要：元の全入力円柱を全合成列に制限し、端点と全頂点の固定構造射を回収する。
方針：同じ円柱の Yoneda 制限と Kan 包含を忘れる全単体の式を使う。
規約：入力は小さい通常の圏。面・退化を含めて独立な選択を導入しない。
使われ方：元の四辺を持つ自然性 square と BF 列の高次整合性。
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
local instance boundarySuspensionPrisms_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の全体円柱の合成列への制限。一次元では自然性 square。 -/
def boundaryAssemblyOriginalSuspensionPrism {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    (Δ[n] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SimplicialNerve PointedSimplicialSet.{u} :=
  homotopySimplexPrism (boundaryAssemblyOriginalSuspensionHomotopy r F) (ULift.up s)

/-- prism の始点は、元の各段の通常の図式を suspension したもの。 -/
lemma boundaryAssemblyOriginalSuspensionPrism_zero {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    SSet.ι₀ ≫ boundaryAssemblyOriginalSuspensionPrism r F s =
      SSet.yonedaEquiv.symm (ULift.up s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor := by
  have hs : pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
      (fun i => boundaryKanRealization_kanComplex r (F.obj i)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor := by
    rw [← Category.assoc, pointedKanInclusion_coherentDiagram]
  have h := homotopySimplexPrism_zero (boundaryAssemblyOriginalSuspensionHomotopy r F)
    (ULift.up s)
  conv at h => rhs; rw [hs]
  exact h

/-- prism の終点は、元の次段の通常の図式そのもの。 -/
lemma boundaryAssemblyOriginalSuspensionPrism_one {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    SSet.ι₁ ≫ boundaryAssemblyOriginalSuspensionPrism r F s =
      SSet.yonedaEquiv.symm (ULift.up s) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1)) := by
  have h := homotopySimplexPrism_one (boundaryAssemblyOriginalSuspensionHomotopy r F)
    (ULift.up s)
  conv at h => rhs; rw [pointedKanInclusion_coherentDiagram]
  exact h

/-- 全合成列の面・退化は、同じ prism の制限として厳密に可換。 -/
lemma boundaryAssemblyOriginalSuspensionPrism_naturality {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (s : (nerve I) _⦋n⦌) :
    (SSet.stdSimplex.map θ ▷ (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F s =
        boundaryAssemblyOriginalSuspensionPrism r F ((nerve I).map θ.op s) :=
  homotopySimplexPrism_naturality (boundaryAssemblyOriginalSuspensionHomotopy r F) θ (ULift.up s)

/-- 全合成列の各頂点で、元の固定 suspension 構造射の辺を厳密に回収する。 -/
lemma boundaryAssemblyOriginalSuspensionPrism_vertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌)
    (a : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
    lift (SSet.const a) (𝟙 (Δ[1] : SSet.{u + 1})) ≫
      boundaryAssemblyOriginalSuspensionPrism r F s =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (boundaryKanAssemblySigma r (F.obj (s.obj (a 0))))).edge := by
  have ha : (SSet.yonedaEquiv.symm (ULift.up s) : (Δ[n] : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u+1,u}).obj (nerve I)).app (Opposite.op ⦋0⦌) a =
      ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj (a 0))) := by
    apply congrArg ULift.up
    exact ComposableArrows.ext₀ rfl
  have h := homotopySimplexPrism_vertex (boundaryAssemblyOriginalSuspensionHomotopy r F)
    (ULift.up s) a
  rw [ha, boundaryAssemblyOriginalSuspensionHomotopy_vertex_edge] at h
  exact h

end SerrePositivity.KST.SConstruction
