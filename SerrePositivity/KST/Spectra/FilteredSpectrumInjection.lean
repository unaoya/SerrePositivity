module

public import SerrePositivity.KST.Spectra.FilteredSpectrumHomotopy
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting

/-!
概要：filtered Ω 列の BF 置換への各段からの厳密な比較射。
方針：cofibrant な源から置換射へ持ち上げ、整数次数の群の余極限比較で計算する。
規約：選択した持ち上げの厳密な自然性は要求せず、誘導する π_* の自然性を示す。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。telescope の有理化写像の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 概要：filtered BF 対象から段ごとの Kan 余極限列への比較。
方針：単射置換の標準射を Kan 列の射として使う。
規約：各段で全単射への RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。各段の注入射を持ち上げる右辺。 -/
def filteredSequenceComparison (D : J ⥤ OmegaSpectrum.{u}) :
    KanSequence.Hom (filteredOmegaSpectrum D).toKanSequence (filteredKanSequence D) :=
  (filteredKanSequence D).cofibrantOmegaProjection (filteredKanSequence_omegaCondition D)

/-- 概要：元の各対象から filtered BF 対象への厳密な射。
方針：元の単射な構造射を使い、余極限への射を単射置換へ持ち上げる。
規約：射の選択は固定するが、選択同士の厳密な自然性を主張しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。telescope の各段からの射。 -/
def filteredSpectrumInjection (D : J ⥤ OmegaSpectrum.{u}) (a : J) :
    D.obj a ⟶ filteredOmegaSpectrum D where
  app := (KanSequence.liftHom (D.obj a).sigma_mono (filteredSequenceComparison D)
    (fun k ↦ (KanSequence.replacementStage (filteredKanSequence D) k).projection_rlp)
    (filteredKanInjection D a)).app
  comm := (KanSequence.liftHom (D.obj a).sigma_mono (filteredSequenceComparison D)
    (fun k ↦ (KanSequence.replacementStage (filteredKanSequence D) k).projection_rlp)
    (filteredKanInjection D a)).comm

/-- 概要：選んだ射を BF 置換の比較射へ合成すると段の余極限への標準射。
方針：cofibrant な源からの持ち上げの計算則を使う。
規約：各段の点つき射の厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。有理化写像の π_* の計算。 -/
theorem filteredSpectrumInjection_comparison (D : J ⥤ OmegaSpectrum.{u}) (a : J) (k : ℕ) :
    (filteredSpectrumInjection D a).app k ≫ filteredLevelComparison D k =
      colimit.ι (levelDiagram D k) a :=
  KanSequence.liftHom_fac (D.obj a).sigma_mono (filteredSequenceComparison D) _ _ k

/-- 概要：各段からの射の整数次数表示は実際の段の余極限への写像。
方針：正次数表示の自然性と、持ち上げの比較式を合成する。
規約：任意の許容段 k と正次数 n+1。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の余極限比較との整合性。 -/
theorem filteredSpectrumInjection_stage (D : J ⥤ OmegaSpectrum.{u}) (a : J)
    (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ)) (hd : degree j k = n + 1)
    (x : homotopyGroup (D.obj a) j) :
    filteredSpectrumStageEquiv D j k n hk hd (homotopyMap (filteredSpectrumInjection D a) j x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (colimit.ι (levelDiagram D k) a).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (positiveStageEquiv (D.obj a) j k n hk hd x) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n (filteredLevelComparison D k).right
    (filteredLevelComparison_piIsomorphism D k) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
      (positiveStageEquiv (filteredOmegaSpectrum D) j k n hk hd
        (homotopyMap (filteredSpectrumInjection D a) j x)) = _
  rw [positiveStageEquiv_natural]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
  let s := positiveStageEquiv (D.obj a) j k n hk hd x
  have hm := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n)
    ((filteredSpectrumInjection D a).app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (filteredLevelComparison D k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint ((filteredSpectrumInjection D a).app k ≫
      filteredLevelComparison D k))) s
  have heq := congrArg (fun f : ((D.obj a).level k).space ⟶ colimit (levelDiagram D k) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) s)
      (filteredSpectrumInjection_comparison D a k)
  exact hm.symm.trans heq

/-- 概要：群の余極限比較は選んだ厳密な各段からの射を誘導する。
方針：両辺を同じ正次数表示へ移し、各段の比較式で一致させる。
規約：全整数次数 j。
使われ方：BF 1978 §2、HA §1.4.2。telescope の標準射と群の局所化の接続。 -/
theorem filteredSpectrumHomotopyIso_ι (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ) (a : J) :
    colimit.ι (spectrumHomotopyGroupDiagram D j) a ≫ (filteredSpectrumHomotopyIso D j).hom =
      GrpCat.ofHom (homotopyMap (filteredSpectrumInjection D a) j) := by
  ext x
  apply (filteredSpectrumStageEquiv D j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).injective
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
    (filteredSpectrumHomotopyIso_ι_stage D j a)) x
  exact h.trans (filteredSpectrumInjection_stage D a j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j) x).symm

/-- 概要：選んだ注入射は整数次数の群では図式の遷移と可換。
方針：群の余極限 cocone の自然性へ比較同型を後合成する。
規約：スペクトルの射の厳密な可換性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の段によらない標準写像。 -/
theorem filteredSpectrumInjection_natural (D : J ⥤ OmegaSpectrum.{u}) (j : ℤ)
    {a b : J} (f : a ⟶ b) :
    (homotopyMap (filteredSpectrumInjection D b) j).comp (homotopyMap (D.map f) j) =
      homotopyMap (filteredSpectrumInjection D a) j := by
  have h := congrArg (fun t ↦ t ≫ (filteredSpectrumHomotopyIso D j).hom)
    (colimit.w (spectrumHomotopyGroupDiagram D j) f)
  rw [Category.assoc, filteredSpectrumHomotopyIso_ι, filteredSpectrumHomotopyIso_ι] at h
  exact congrArg GrpCat.Hom.hom h

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
