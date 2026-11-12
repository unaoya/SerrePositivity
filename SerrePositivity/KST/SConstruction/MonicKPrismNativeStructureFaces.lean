module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeStructureTriangle
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeDirectStructureTriangle
public import SerrePositivity.KST.SConstruction.FamilyCompStructRealization

/-! # 保存済み円柱の構造適合三角形の実三面
概要：BF 合成側と直接厳密化側の実構造三角形から、元の円柱の全実写像を回収する。
方針：同じ全二単体を復号し、表示移送が全時刻の写像を変えないことを使う。
規約：両側とも同じ元の適合円柱を第一面に保ち、全段の既存円柱の実像を回収する。
使われ方：単射源の構造射制限による全段比較の相対持ち上げ。
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

/-- BF 合成側の保存済み各段円柱の全実構造三角形。 -/
def monicKPrismNativeStructureMap (n : ℕ) :=
  familyCompStructRealization (monicKPrismNativeStructureTriangle F f g n)

/-- 第一面は元の合成射の全適合円柱。 -/
lemma monicKPrismNativeStructureMap_first (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismNativeStructureMap F f g n =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h :=
  (familyCompStructRealization_first _).trans
    (monicKPrismNativeOriginalCompatibility_h F f g n)

/-- 第二面は保存済み前段円柱全体の元の構造射像。 -/
lemma monicKPrismNativeStructureMap_previous (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismNativeStructureMap F f g n =
      (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (familyCompStructRealization_second _).trans (familyHomotopyEndpointTransport_h _ _ _)

/-- 合成面は保存済み次段円柱全体の元の源構造射への制限。 -/
lemma monicKPrismNativeStructureMap_projected (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativeStructureMap F f g n =
      (monicKPrismNativeCompositeCorrectionData F f g (n + 1)).homotopy.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyCompStructRealization_direct _

/-- 直接厳密化側の保存済み各段円柱の全実構造三角形。 -/
def monicKPrismNativeDirectStructureMap (n : ℕ) :=
  familyCompStructRealization (monicKPrismNativeDirectStructureTriangle F f g n)

/-- 直接厳密化側も同じ元の全適合円柱を第一面に保つ。 -/
lemma monicKPrismNativeDirectStructureMap_first (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 2) ≫
        monicKPrismNativeDirectStructureMap F f g n =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h :=
  (familyCompStructRealization_first _).trans
    (monicKPrismNativeOriginalCompatibility_h F f g n)

/-- 第二面は直接厳密化の保存済み前段円柱の全構造射像。 -/
lemma monicKPrismNativeDirectStructureMap_previous (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismNativeDirectStructureMap F f g n =
      (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (familyCompStructRealization_second _).trans (familyHomotopyEndpointTransport_h _ _ _)

/-- 合成面も直接厳密化の保存済み次段円柱の全源制限を保つ。 -/
lemma monicKPrismNativeDirectStructureMap_projected (n : ℕ) :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 1) ≫
        monicKPrismNativeDirectStructureMap F f g n =
      (monicKPrismNativeDirectCorrectionData F f g (n + 1)).homotopy.h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space :=
  familyCompStructRealization_direct _

end SerrePositivity.KST.SConstruction
