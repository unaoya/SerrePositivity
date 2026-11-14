module

public import SerrePositivity.KST.Spectra.SpectrumMappingVertices
public import SerrePositivity.KST.Spectra.SuspensionComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedMappingLaws

/-!
概要：Ω スペクトルの写像空間の単体的合成。
方針：段ごとの合成の構造整合性を検査し、切断写像空間の極限へ持ち上げる。
規約：合成は通常の単体集合の直積を定義域とする。
使われ方：BF 1978 §2、HTT A.3.3。Sp の単体的圏。
-/

@[expose] public section

universe u

open CategoryTheory SSet MonoidalCategory

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 概要：二つのスペクトルの整合写像を指定段で合成する。
方針：各段評価をテンソルし、その段の単体的合成を使う。
規約：順に X から Y、Y から Z の写像を取る。
使われ方：BF 1978 §2、HTT A.3.3。極限への合成の構成。 -/
def compositionFamily (X Y Z : OmegaSpectrum.{u}) (n : ℕ) :
    mappingSpace X Y ⊗ mappingSpace Y Z ⟶
      (PointedObject.basedHom (X.level n).space (Z.level n).space).right :=
  (evaluation X Y n ⊗ₘ evaluation Y Z n) ≫
    eComp SSet (X.level n).space (Y.level n).space (Z.level n).space

/-- 概要：段ごとの合成はスペクトルの構造射との整合条件を満たす。
方針：前合成・後合成の整合性と suspension の豊穣関手性を使う。
規約：Ω 条件は使わない。
使われ方：BF 1978 §2、HTT A.3.3。写像空間の極限への持ち上げ。 -/
theorem compositionFamily_condition (X Y Z : OmegaSpectrum.{u}) (n : ℕ) :
    compositionFamily X Y Z (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Z.level (n + 1)).space =
      compositionFamily X Y Z n ≫ mappingStep X Z n := by
  have ha : evaluation X Y (n + 1) ≫
      eHomWhiskerRight SSet (X.sigma n) (Y.level (n + 1)).space =
      evaluation X Y n ≫
        suspensionEnrichedFunctor.map (X.level n).space (Y.level n).space ≫
          eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n) := by
    rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq]
    exact evaluation_condition X Y n
  have hb : evaluation Y Z (n + 1) ≫
      eHomWhiskerRight SSet (Y.sigma n) (Z.level (n + 1)).space =
      evaluation Y Z n ≫
        suspensionEnrichedFunctor.map (Y.level n).space (Z.level n).space ≫
          eHomWhiskerLeft SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space) (Z.sigma n) := by
    rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq]
    exact evaluation_condition Y Z n
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_compatible_comp SSet suspensionEnrichedFunctor
    (X.sigma n) (Y.sigma n) (Z.sigma n)
    (evaluation X Y n) (evaluation X Y (n + 1))
    (evaluation Y Z n) (evaluation Y Z (n + 1)) ha hb
  simpa only [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerLeft_eq,
    compositionFamily, mappingStep, suspensionEnrichedFunctor, Category.assoc] using h

/-- 概要：スペクトルの写像空間の単体的合成。
方針：構造条件を満たす段ごとの合成族を極限へ持ち上げる。
規約：厳密な射の段ごとの合成との一致は評価によって検査する。
使われ方：BF 1978 §2、HTT A.3.3。Sp の単体的圏の合成。 -/
def mappingComposition (X Y Z : OmegaSpectrum.{u}) :
    mappingSpace X Y ⊗ mappingSpace Y Z ⟶ mappingSpace X Z :=
  TruncatedMapping.familyLift (fun n ↦ (X.level n).space) (fun n ↦ (Z.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Z)
    (compositionFamily X Y Z) (compositionFamily_condition X Y Z)

/-- 概要：写像空間の合成を指定段に評価するとその段の合成になる。
方針：極限への持ち上げの評価計算を用いる。
規約：単体集合の射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。単位律・結合律の評価による証明。 -/
@[reassoc (attr := simp)]
theorem mappingComposition_evaluation (X Y Z : OmegaSpectrum.{u}) (n : ℕ) :
    mappingComposition X Y Z ≫ evaluation X Z n = compositionFamily X Y Z n :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
