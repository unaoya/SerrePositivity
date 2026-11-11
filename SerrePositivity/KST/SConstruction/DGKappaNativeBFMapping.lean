module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFOmegaSpectrum
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
open SerrePositivity.InfinityCategories DifferentialGraded NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 各段の元の全 Hom 作用は、同じ BF 構造射と厳密に整合する。 -/
lemma dgKappaNativeBFMapping_condition (X Y : DGKappaNativeBFFiniteInput.{u, v} R D I)
    (n : ℕ) :
    (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).map X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).sigma n)
          ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y).level (n + 1)).space =
      (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map X Y ≫
        OmegaSpectrum.mappingStep (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y) n := by
  have h := dgKappaNativeBFFiniteStructureMap_whisker.{u, v} R D I n X Y
  let : SimplicialCategory PointedSimplicialSet.{max (u + 1) v} :=
    PointedEnrichment.simplicialCategory
  change ((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map X Y ≫
    (suspensionHom ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).level n).space
      ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y).level n).space).right) ≫
      eHomWhiskerLeft SSet
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).level n).space)
        ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y).sigma n) =
    (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).map X Y ≫
      eHomWhiskerRight SSet ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).sigma n)
        ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y).level (n + 1)).space at h
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq] at h
  exact h.symm.trans (Category.assoc _ _ _)

/-- 同じ四頂点像の全 Hom の作用を、同じ実 BF 写像空間へ束ねる。 -/
def dgKappaNativeBFMapping (X Y : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (X ⟶[SSet.{max (u + 1) v}] Y) ⟶
      OmegaSpectrum.mappingSpace (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
        (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y) :=
  TruncatedMapping.familyLift
    (fun n => ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).level n).space)
    (fun n => ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y).level n).space)
    (fun n => _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).level n).space)
    (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X).sigma
    (OmegaSpectrum.mappingStep (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
      (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y))
    (fun n => (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map X Y)
    (dgKappaNativeBFMapping_condition.{u, v} R D I X Y)

/-- 同じ写像空間への作用を評価すると、元の各段の全 Hom 作用へ戻る。 -/
lemma dgKappaNativeBFMapping_evaluation (X Y : DGKappaNativeBFFiniteInput.{u, v} R D I)
    (n : ℕ) :
    dgKappaNativeBFMapping.{u, v} R D I X Y ≫
        OmegaSpectrum.evaluation (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I X)
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I Y) n =
      (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).map X Y :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

end SerrePositivity.KST.SConstruction
