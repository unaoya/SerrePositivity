module
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositionNativeTriangles
public import SerrePositivity.KST.SConstruction.CompositionStringPairParameters
public import SerrePositivity.KST.SConstruction.PointedMappingSourceWhiskers

/-! # 元の全三角形族の第一面・合成面と保存済み raw 円柱
概要：全精密化の比較三角形の二面を、保存済み補正列に現れる同じ実円柱へ照合する。
方針：源の制限と後合成を交換し、二入力への射対と合成射への射影を使う。
規約：円柱の全時刻を等号で保持し、成分の等式へ忘れない。
使われ方：元の実比較を全段の BF 補正 trace へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance monicKPrismNativeTraceFacesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 第一面は、合成補正の射影 trace に現れる同じ第一適合円柱の引き戻し。 -/
lemma monicKPrismCompositionNativeTriangle_first_trace :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeFirstCompatibility F f g r := by
  rw [monicKPrismCompositionNativeTriangle_first]
  simp only [kKanCompositionFirstNativeCylinder, constantFamilyHomotopyWhisker,
    monicKPrismCompositeFirstCompatibility, monicKPrismRawSequenceCompatibility_h,
    monicKPrismSpecifiedCompatibilityFamily_h, Category.assoc,
    ← comp_whiskerRight_assoc, compositionStringPair_first]
  exact congrArg (fun h => (nerveMap (compositionStringFirst f g) ▷ (Δ[1] : SSet.{u})) ≫
    (kKanOriginalPrismSpecifiedCompatibilityFamily r F f).h ≫ h)
    (pointedMapping_post_pre
      (PointedSimplicialSet.circle.{u} ◁ (monicKKanSequenceProjection (F.obj x)).app r)
      (kKanSequenceLevelMap (F.map g) (r + 1)))

/-- 合成面は、合成射の元の raw 適合円柱そのものの引き戻し。 -/
lemma monicKPrismCompositionNativeTriangle_composite_trace :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismCompositionNativeTriangle r F f g =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility r F (f ≫ g)).h := by
  rw [monicKPrismCompositionNativeTriangle_composite]
  simp only [kKanCompositionCompositeNativeCylinder, constantFamilyHomotopyWhisker,
    monicKPrismRawSequenceCompatibility_h, monicKPrismSpecifiedCompatibilityFamily_h,
    Category.comp_id, Category.assoc]

end SerrePositivity.KST.SConstruction
