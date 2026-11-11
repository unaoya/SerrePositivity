module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingLaws
public import SerrePositivity.KST.Spectra.SpectrumMappingComposition

/-!
概要：一般の Kan 列を標的とする元の整合写像空間に、BF 豊穣 Hom の全パラメータで合成する。
方針：各段の合成の構造条件を検査し、全整合族へ厳密に持ち上げる。
規約：標的の Ω 条件・単射構造は不要。使われ方：Hom-end 比較の源変数の豊穣自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
local instance rawCompositionPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- BF の Hom と一般の Kan 列への整合写像を各段で合成する。 -/
def compositionFamily (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    OmegaSpectrum.mappingSpace X Y ⊗ space Y Z ⟶
      (PointedObject.basedHom (X.level n).space (Z.level n).space).right :=
  (OmegaSpectrum.evaluation X Y n ⊗ₘ evaluation Y Z n) ≫
    eComp SSet (X.level n).space (Y.level n).space (Z.level n).space

/-- 概要：段ごとの合成はスペクトルの構造射との整合条件を満たす。
方針：前合成・後合成の整合性と suspension の豊穣関手性を使う。
規約：Ω 条件は使わない。
使われ方：BF 1978 §2、HTT A.3.3。写像空間の極限への持ち上げ。 -/
theorem compositionFamily_condition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    compositionFamily X Y Z (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Z.level (n + 1)).space =
      compositionFamily X Y Z n ≫ step X Z n := by
  have ha : OmegaSpectrum.evaluation X Y (n + 1) ≫
      eHomWhiskerRight SSet (X.sigma n) (Y.level (n + 1)).space =
      OmegaSpectrum.evaluation X Y n ≫
        suspensionEnrichedFunctor.map (X.level n).space (Y.level n).space ≫
          eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n) := by
    rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq]
    exact OmegaSpectrum.evaluation_condition X Y n
  have hb : evaluation Y Z (n + 1) ≫
      eHomWhiskerRight SSet (Y.sigma n) (Z.level (n + 1)).space =
      evaluation Y Z n ≫
        suspensionEnrichedFunctor.map (Y.level n).space (Z.level n).space ≫
          eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space) (Z.sigma n) := by
    rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq]
    exact evaluation_condition Y Z n
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_compatible_comp SSet suspensionEnrichedFunctor
    (X.sigma n) (Y.sigma n) (Z.sigma n)
    (OmegaSpectrum.evaluation X Y n) (OmegaSpectrum.evaluation X Y (n + 1))
    (evaluation Y Z n) (evaluation Y Z (n + 1)) ha hb
  simpa only [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    compositionFamily, step, suspensionEnrichedFunctor, Category.assoc] using h

/-- 概要：スペクトルの写像空間の単体的合成。
方針：構造条件を満たす段ごとの合成族を極限へ持ち上げる。
規約：厳密な射の段ごとの合成との一致は評価によって検査する。
使われ方：BF 1978 §2、HTT A.3.3。Sp の単体的圏の合成。 -/
def composition (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) :
    OmegaSpectrum.mappingSpace X Y ⊗ space Y Z ⟶ space X Z :=
  TruncatedMapping.familyLift (fun n ↦ (X.level n).space) (fun n ↦ (Z.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (step X Z)
    (compositionFamily X Y Z) (compositionFamily_condition X Y Z)

/-- 概要：写像空間の合成を指定段に評価するとその段の合成になる。
方針：極限への持ち上げの評価計算を用いる。
規約：単体集合の射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。単位律・結合律の評価による証明。 -/
@[reassoc (attr := simp)]
theorem composition_evaluation (X Y : OmegaSpectrum.{u}) (Z : KanSequence.{u}) (n : ℕ) :
    composition X Y Z ≫ evaluation X Z n = compositionFamily X Y Z n :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
