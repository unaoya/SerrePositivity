module

public import SerrePositivity.KST.Spectra.D3StageStructureCoherenceCriterion

/-!
概要：実段比較の構造不一致を、保持した模型補正の明示的な共役として回収する。
方針：既証の貼合せと次段三角形を可逆因子で解き、同じ指定値で等式を得る。
規約：補正を恒等とは置かず、通常 loop 像へ持ち上がるとも仮定しない。
使われ方：BF 全体へ進む際に、比較へ必要な補正とその持ち上げ問題を正確に保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra

/-- 二つの指定貼合せから、構造不一致を同じ模型補正の共役として回収する。 -/
lemma d3Iso_pasting_structure_defect {V : Type v} [Category V]
    {A B C D E F G : V} (a : A ≅ B) (s : B ≅ D) (r : A ≅ C)
    (b : C ≅ D) (q : C ≅ E) (u : E ≅ F) (d : D ≅ F) (c : F ≅ G) (w : E ≅ G)
    (hp : ((a ≪≫ s) ≪≫ d) ≪≫ c = (r ≪≫ q) ≪≫ w)
    (ht : b ≪≫ d = q ≪≫ u) :
    a ≪≫ s = ((r ≪≫ q) ≪≫ ((u ≪≫ c) ≪≫ w.symm).symm) ≪≫ (q.symm ≪≫ b) := by
  have hqb : q.symm ≪≫ b = u ≪≫ d.symm := by
    calc
      _ = q.symm ≪≫ ((b ≪≫ d) ≪≫ d.symm) := by
        simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
      _ = _ := by
        rw [ht]
        simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  calc
    _ = ((((a ≪≫ s) ≪≫ d) ≪≫ c) ≪≫ c.symm) ≪≫ d.symm := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = (((r ≪≫ q) ≪≫ w) ≪≫ c.symm) ≪≫ d.symm := by rw [hp]
    _ = _ := by
      rw [hqb]
      simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
        Iso.symm_self_id_assoc]

namespace OmegaSpectrum.AdjointLoopRelativeBF
local instance d3DefectSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 実段比較の構造不一致は、同じ右射影で移した模型補正の逆を挿入した値そのもの。
補正の通常 loop 以前への持ち上げや全 BF 関手同型は、この等式だけでは供給しない。 -/
lemma commonChosenStageRefinedSource_structure_defect (n : ℕ) :
    commonChosenStageRefinedSourceNormalizedIso.{u} n ≪≫
      (commonChosenStageStructureDiagramIso n).postcomp
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) =
    ((commonProjectionStructureRefinedIso n ≪≫ commonProjectionStructureLoopQIso n) ≪≫
      (commonChosenStageLoopModelCorrection n).symm) ≪≫
        ((commonProjectionStructureLoopQIso n).symm ≪≫
          commonChosenStageLoopedRefinedSourceIso n) := by
  exact d3Iso_pasting_structure_defect
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
