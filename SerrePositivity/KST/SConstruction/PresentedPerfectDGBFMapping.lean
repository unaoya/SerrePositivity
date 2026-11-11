module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFOmegaSpectrum
public import SerrePositivity.KST.Spectra.SpectrumSimplicialCategory

/-! # 元の厳密 dg 全 Hom から BF スペクトル写像空間への作用
概要：全実再帰段の同じ豊穣作用を、元の BF 写像空間へ持ち上げる。
方針：構造射の全 Hom 自然性を写像塔の整合条件に照合する。
規約：零次射だけへの制限はしない。使われ方：厳密豊穣 BF K 関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 各段の元の全 Hom 作用は、同じ BF 構造射と厳密に整合する。 -/
lemma presentedPerfectDGBFMapping_condition (X Y : PerfDGInput.{u, v} A) (n : ℕ) :
    (presentedPerfectDGBFLevelFunctor A (n + 1)).map X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((presentedPerfectDGBFOmegaSpectrum A X).sigma n)
          ((presentedPerfectDGBFOmegaSpectrum A Y).level (n + 1)).space =
      (presentedPerfectDGBFLevelFunctor A n).map X Y ≫
        OmegaSpectrum.mappingStep (presentedPerfectDGBFOmegaSpectrum A X)
          (presentedPerfectDGBFOmegaSpectrum A Y) n := by
  have h := presentedPerfectDGBFStructureMap_whisker A n X Y
  let : SimplicialCategory PointedSimplicialSet.{max (u + 1) v} :=
    PointedEnrichment.simplicialCategory
  change ((presentedPerfectDGBFLevelFunctor A n).map X Y ≫
    (suspensionHom ((presentedPerfectDGBFOmegaSpectrum A X).level n).space
      ((presentedPerfectDGBFOmegaSpectrum A Y).level n).space).right) ≫
      eHomWhiskerLeft SSet
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((presentedPerfectDGBFOmegaSpectrum A X).level n).space)
        ((presentedPerfectDGBFOmegaSpectrum A Y).sigma n) =
    (presentedPerfectDGBFLevelFunctor A (n + 1)).map X Y ≫
      eHomWhiskerRight SSet ((presentedPerfectDGBFOmegaSpectrum A X).sigma n)
        ((presentedPerfectDGBFOmegaSpectrum A Y).level (n + 1)).space at h
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq] at h
  exact h.symm.trans (Category.assoc _ _ _)

/-- 元の全 dg 入力 Hom の作用を、同じ実 BF 写像空間へ束ねる。 -/
def presentedPerfectDGBFMapping (X Y : PerfDGInput.{u, v} A) :
    (X ⟶[SSet.{max (u + 1) v}] Y) ⟶
      OmegaSpectrum.mappingSpace (presentedPerfectDGBFOmegaSpectrum A X)
        (presentedPerfectDGBFOmegaSpectrum A Y) :=
  TruncatedMapping.familyLift
    (fun n => ((presentedPerfectDGBFOmegaSpectrum A X).level n).space)
    (fun n => ((presentedPerfectDGBFOmegaSpectrum A Y).level n).space)
    (fun n => _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((presentedPerfectDGBFOmegaSpectrum A X).level n).space)
    (presentedPerfectDGBFOmegaSpectrum A X).sigma
    (OmegaSpectrum.mappingStep (presentedPerfectDGBFOmegaSpectrum A X)
      (presentedPerfectDGBFOmegaSpectrum A Y))
    (fun n => (presentedPerfectDGBFLevelFunctor A n).map X Y)
    (presentedPerfectDGBFMapping_condition A X Y)

/-- 同じ写像空間への作用を評価すると、元の各段の全 Hom 作用へ戻る。 -/
@[reassoc (attr := simp)]
lemma presentedPerfectDGBFMapping_evaluation (X Y : PerfDGInput.{u, v} A) (n : ℕ) :
    presentedPerfectDGBFMapping A X Y ≫
        OmegaSpectrum.evaluation (presentedPerfectDGBFOmegaSpectrum A X)
          (presentedPerfectDGBFOmegaSpectrum A Y) n =
      (presentedPerfectDGBFLevelFunctor A n).map X Y :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

end SerrePositivity.KST.SConstruction
