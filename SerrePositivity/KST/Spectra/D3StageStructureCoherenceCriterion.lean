module

public import SerrePositivity.KST.Spectra.D3StageLoopedUnitTriangle

/-!
概要：同じ既存段比較の BF 構造整合に残る条件を、保持した模型比較の補正同型で特徴付ける。
方針：構成済み二つの指定三角形の可逆因子を打ち消し、残る同じ模型比較を明示する。
規約：補正同型の恒等性を仮定しない。この判定を BF 全体の比較の完成とは数えない。
使われ方：段の貼合せから全 BF 比較へ進む際に、未証明の整合条件を取り違えず検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 同じ二つの貼合せの可逆因子を打ち消すと、構造正方形と表示同型の整合が同値となる。 -/
lemma d3Iso_pasting_coherence_iff {V : Type v} [Category V]
    {A B C D E F G : V} (a : A ≅ B) (s : B ≅ D) (r : A ≅ C)
    (b : C ≅ D) (q : C ≅ E) (u : E ≅ F) (d : D ≅ F) (c : F ≅ G) (w : E ≅ G)
    (hp : ((a ≪≫ s) ≪≫ d) ≪≫ c = (r ≪≫ q) ≪≫ w)
    (ht : b ≪≫ d = q ≪≫ u) :
    (a ≪≫ s = r ≪≫ b) ↔ u ≪≫ c = w := by
  constructor
  · intro hs
    have h : (r ≪≫ q) ≪≫ (u ≪≫ c) = (r ≪≫ q) ≪≫ w := by
      calc
        _ = r ≪≫ ((q ≪≫ u) ≪≫ c) := by simp only [Iso.trans_assoc]
        _ = r ≪≫ ((b ≪≫ d) ≪≫ c) := by rw [← ht]
        _ = ((r ≪≫ b) ≪≫ d) ≪≫ c := by simp only [Iso.trans_assoc]
        _ = _ := by rw [← hs]; exact hp
    apply Iso.ext
    have hh := congrArg (fun i : A ≅ G ↦ i.hom) h
    have hh' : (r.hom ≫ q.hom) ≫ (u.hom ≫ c.hom) = (r.hom ≫ q.hom) ≫ w.hom := by
      simpa only [Iso.trans_hom, Category.assoc] using hh
    exact (cancel_epi (r.hom ≫ q.hom)).mp hh'
  · intro hu
    have h : ((a ≪≫ s) ≪≫ d) ≪≫ c = ((r ≪≫ b) ≪≫ d) ≪≫ c := by
      calc
        _ = (r ≪≫ q) ≪≫ w := hp
        _ = (r ≪≫ q) ≪≫ (u ≪≫ c) := by rw [hu]
        _ = r ≪≫ ((q ≪≫ u) ≪≫ c) := by simp only [Iso.trans_assoc]
        _ = r ≪≫ ((b ≪≫ d) ≪≫ c) := by rw [← ht]
        _ = _ := by simp only [Iso.trans_assoc]
    apply Iso.ext
    have hh := congrArg (fun i : A ≅ G ↦ i.hom) h
    have hh' : (a.hom ≫ s.hom) ≫ (d.hom ≫ c.hom) =
        (r.hom ≫ b.hom) ≫ (d.hom ≫ c.hom) := by
      simpa only [Iso.trans_hom, Category.assoc] using hh
    exact (cancel_mono (d.hom ≫ c.hom)).mp hh'

/-- 二つの指定同型の差の補正が恒等であることと、同じ指定値の一致は同値。 -/
lemma d3Iso_difference_refl_iff {V : Type v} [Category V] {A B : V} (a b : A ≅ B) :
    a ≪≫ b.symm = Iso.refl A ↔ a = b := by
  constructor
  · intro h
    have ht := congrArg (fun e ↦ e ≪≫ b) h
    simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using ht
  · rintro rfl
    exact Iso.self_symm_id _

/-- 貼合せで残る構造整合を、指定模型比較の補正の恒等性で判定する。 -/
lemma d3Iso_pasting_correction_iff {V : Type v} [Category V]
    {A B C D E F G : V} (a : A ≅ B) (s : B ≅ D) (r : A ≅ C)
    (b : C ≅ D) (q : C ≅ E) (u : E ≅ F) (d : D ≅ F) (c : F ≅ G) (w : E ≅ G)
    (hp : ((a ≪≫ s) ≪≫ d) ≪≫ c = (r ≪≫ q) ≪≫ w)
    (ht : b ≪≫ d = q ≪≫ u) :
    (a ≪≫ s = r ≪≫ b) ↔ (u ≪≫ c) ≪≫ w.symm = Iso.refl E :=
  (d3Iso_pasting_coherence_iff a s r b q u d c w hp ht).trans
    (d3Iso_difference_refl_iff (u ≪≫ c) w).symm

namespace OmegaSpectrum.AdjointLoopRelativeBF
local instance d3CriterionSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ次段始点表示の loop 像と保持した模型比較を、実次段像の始点表示と照合する補正。 -/
def commonChosenStageLoopModelCorrection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet
      (d3StageKanEnriched.{u} (n + 2))).comp SSet pointedKanLoopEnrichedFunctor).comp
        SSet pointedKanLoopEnrichedFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (((commonOriginalEnriched.comp SSet (d3StageKanEnriched (n + 2))).comp
        SSet pointedKanLoopEnrichedFunctor).comp SSet pointedKanLoopEnrichedFunctor)) :=
  (commonChosenStageLoopedCanonicalUnitIso n ≪≫
    (commonChosenStageLoopImageComparison n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) ≪≫
        (commonChosenStageCanonicalImageUnitIso n).symm

/-- 同じ既存段比較が BF 構造を保つことは、保持した模型比較の補正の恒等性と同値。
この恒等性の証明や BF 全体への持ち上げを、判定定理だけで供給したとは扱わない。 -/
lemma commonChosenStageRefinedSource_structure_iff (n : ℕ) :
    (commonChosenStageRefinedSourceNormalizedIso.{u} n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    commonProjectionStructureRefinedIso n ≪≫ commonChosenStageLoopedRefinedSourceIso n) ↔
      commonChosenStageLoopModelCorrection.{u} n = Iso.refl _ := by
  exact d3Iso_pasting_correction_iff
    (commonChosenStageRefinedSourceNormalizedIso n)
    ((commonChosenStageStructureDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonProjectionStructureRefinedIso n) (commonChosenStageLoopedRefinedSourceIso n)
    (commonProjectionStructureLoopQIso n) (commonChosenStageLoopedCanonicalUnitIso n)
    ((commonChosenStageLoopedCanonicalDiagramIso n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    ((commonChosenStageLoopImageComparison n).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0))
    (commonChosenStageCanonicalImageUnitIso n)
    (commonChosenStageRefinedSourceNormalized_pasting n)
    (commonChosenStageLoopedRefinedSource_triangle n)

end OmegaSpectrum.AdjointLoopRelativeBF
end SerrePositivity.KST.Spectra
