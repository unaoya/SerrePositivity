module

public import SerrePositivity.KST.Spectra.FilteredOmegaSpectrum
public import SerrePositivity.KST.Spectra.FilteredHomotopyGroups
public import SerrePositivity.KST.Spectra.SpectrumBoundary

/-!
概要：filtered Ω 列の BF 置換の整数次数群は元の整数次数群の余極限。
方針：固定した正次数の段表示、段の群の余極限、および単射置換の比較同型を合成する。
規約：群の圏の同型を構成し、Sp の ∞ 余極限の普遍性は主張しない。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。L9d の telescope の整数次数の計算。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 概要：Ω スペクトルの図式の各整数次数の群の図式。
方針：既存の整数次数ホモトピー関手を後合成する。
規約：可換性は忘れて群の圏に値を取る。
使われ方：BF 1978 §2、HA §1.4.2。filtered π_* の比較の始域。 -/
abbrev spectrumHomotopyGroupDiagram (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) : J ⥤ GrpCat.{u} :=
  D ⋙ homotopyFunctor j ⋙ forget₂ CommGrpCat GrpCat

/-- 概要：整数次数群の filtered diagram は群の余極限を持つ。
方針：群の filtered colimit の既存の実構成を使う。
規約：値の可換性に依存しない。
使われ方：BF 1978 §2、HA §1.4.2。余極限の比較同型の定義域。 -/
instance spectrumHomotopyGroupDiagram_hasColimit (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) :
    HasColimit (spectrumHomotopyGroupDiagram D j) :=
  ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u} (spectrumHomotopyGroupDiagram D j)⟩

/-- 概要：整数次数群の図式と固定した正次数の段の群の図式の自然同型。
方針：自然な正次数の段表示を各成分に使う。
規約：k は任意の許容段で、実際の次数は n+1。
使われ方：BF 1978 §2、HA §1.4.2。整数次数を段の filtered colimit の計算へ還元する。 -/
def spectrumHomotopyDiagramStageIso (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    spectrumHomotopyGroupDiagram D j ≅ pointedHomotopyGroupDiagram (levelDiagram D k) n :=
  NatIso.ofComponents (fun a ↦ (positiveStageEquiv (D.obj a) j k n hk hd).toGrpIso)
    (fun {a b} f ↦ by
      ext x
      exact positiveStageEquiv_natural (D.map f) j k n hk hd x)

/-- 概要：filtered Ω 列の BF 置換の各段から元の段ごとの余極限への比較射。
方針：Kan Ω 列の単射置換の比較射を使う。
規約：全ての段で全単射への RLP を持つ。
使われ方：BF 1978 §2、HA §1.4.2。整数次数群と余極限の段の群の比較。 -/
def filteredLevelComparison (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    ((filteredOmegaSpectrum D).level k).space ⟶ colimit (levelDiagram D k) :=
  ((filteredKanSequence D).replacementProjection).app k

/-- 概要：filtered Ω 列の単射置換の段の比較射は全基点 π_* 同型。
方針：単射置換の比較射の全単射 RLP から構成済みの同型性を使う。
規約：零次数も含む。
使われ方：BF 1978 §2、HA §1.4.2。群の余極限の計算へ単射置換を反映する。 -/
theorem filteredLevelComparison_piIsomorphism (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (filteredLevelComparison D k).right :=
  KanSequence.replacementProjection_piIsomorphism (filteredKanSequence D) k

/-- 概要：filtered Ω 列の BF 対象の整数次数群と余極限の正次数の段の群の同型。
方針：整数次数の正次数表示と、単射置換の比較射の段ごとの群同型を合成する。
規約：k は任意の許容段。
使われ方：BF 1978 §2、HA §1.4.2。telescope の群の計算の比較先。 -/
def filteredSpectrumStageEquiv (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) (k n : ℕ)
    (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1) :
    homotopyGroup (filteredOmegaSpectrum D) j ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (colimit (levelDiagram D k)).right n
        (colimit (levelDiagram D k)).basepoint :=
  (positiveStageEquiv (filteredOmegaSpectrum D) j k n hk hd).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (filteredLevelComparison D k).right
      (filteredLevelComparison_piIsomorphism D k) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _))

/-- 概要：元の整数次数群の filtered colimit と filtered Ω 列の BF 対象の整数次数群の同型。
方針：図式の段表示、段の群の余極限比較、単射置換の比較同型を順に合成する。
規約：全整数次数 j。群の圏の同型として述べる。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。L9d の有理化の π_* 計算。 -/
def filteredSpectrumHomotopyIso (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) :
    colimit (spectrumHomotopyGroupDiagram D j) ≅
      GrpCat.of (homotopyGroup (filteredOmegaSpectrum D) j) :=
  HasColimit.isoOfNatIso (spectrumHomotopyDiagramStageIso D j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)) ≪≫
      filteredPointedHomotopyGroupIso (levelDiagram D (boundaryStage j)) (boundaryIndex j) ≪≫
        (filteredSpectrumStageEquiv D j (boundaryStage j) (boundaryIndex j)
          (boundaryStage_admissible j) (boundaryStage_degree j)).toGrpIso.symm

/-- 概要：整数次数の余極限比較を各段から正次数表示へ移すと実際の段の余極限射になる。
方針：図式の自然同型と段の群の余極限比較の成分式を合成する。
規約：連結射と同じ boundaryStage・boundaryIndex で計算する。
使われ方：BF 1978 §2、HA §1.4.2。telescope への各段の π_* 写像の計算。 -/
theorem filteredSpectrumHomotopyIso_ι_stage (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) (a : J) :
    colimit.ι (spectrumHomotopyGroupDiagram D j) a ≫ (filteredSpectrumHomotopyIso D j).hom ≫
      (filteredSpectrumStageEquiv D j (boundaryStage j) (boundaryIndex j)
        (boundaryStage_admissible j) (boundaryStage_degree j)).toGrpIso.hom =
    (spectrumHomotopyDiagramStageIso D j (boundaryStage j) (boundaryIndex j)
      (boundaryStage_admissible j) (boundaryStage_degree j)).hom.app a ≫
        GrpCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := boundaryIndex j)
          (colimit.ι (levelDiagram D (boundaryStage j)) a).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)) := by
  simp only [filteredSpectrumHomotopyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [HasColimit.ι_isoOfNatIso_hom_assoc, filteredPointedHomotopyGroupIso_ι]

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
