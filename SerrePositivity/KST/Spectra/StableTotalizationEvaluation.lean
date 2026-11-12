module

public import SerrePositivity.KST.Spectra.OrdinaryTotalizationSpectrum
public import SerrePositivity.KST.Spectra.StageComparisonNaturality

/-!
概要：通常 Tot の BF 模型の整数次数の群を、指定した十分高い通常 Tot の段で計算する。
方針：任意段表示、次数の移送、BF 射影の π 同型を合成する。
規約：j+k=r+1 を明示し、実際の正次数の群を使う。極限の完全性は後続で移す。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。通常 Tot の Milnor 完全列の安定化。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.KST.Spectra.TotalizationMilnor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (D : CosimplicialObject KanSequence.{u}) (hD : KanSequence.TotalizationReedy D)
  (hΩ : ∀ j, (D.obj j).OmegaCondition)

/-- BF 模型の各段から、通常 Tot そのものへの実際の射影。 -/
def levelProjection (k : ℕ) :
    ((KanSequence.totalizationSpectrum D hD hΩ).level k).space ⟶
      PointedTotalization.obj (D ⋙ KanSequence.levelEvaluation k) :=
  (KanSequence.replacementProjection (KanSequence.totalizationKan D hD)).app k

/-- 通常 Tot への BF 射影は全基点 π 同型。 -/
lemma levelProjection_piIsomorphism (k : ℕ) :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (levelProjection D hD hΩ k).right := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  exact KanSequence.replacementProjection_piIsomorphism (KanSequence.totalizationKan D hD) k

/-- BF の整数次数の群から、元の通常 Tot の指定された正次数の群への同型。 -/
def evaluation (j : ℤ) (k r : ℕ) (hk : j + (k : ℤ) = (r + 1 : ℕ)) :
    letI := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
    OmegaSpectrum.homotopyGroup (KanSequence.totalizationSpectrum D hD hΩ) j ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedTotalization.obj (D ⋙ KanSequence.levelEvaluation k)).right r
        (PointedTotalization.obj (D ⋙ KanSequence.levelEvaluation k)).basepoint := by
  let := PointedTotalization.kanComplex (D ⋙ KanSequence.levelEvaluation k)
      ((CosimplicialHornFibration.terminal_iff _).mp (hD k))
  let S := KanSequence.totalizationSpectrum D hD hΩ
  let e := OmegaSpectrum.homotopyGroupEquivAt S j k (by omega)
  have he : OmegaSpectrum.degree j k = r + 1 := by
    unfold OmegaSpectrum.degree
    omega
  exact ((e.trans (OmegaSpectrum.levelHomotopyCongr S rfl he)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism r (levelProjection D hD hΩ k).right
      (levelProjection_piIsomorphism D hD hΩ k)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (levelProjection D hD hΩ k))))

end
end SerrePositivity.KST.Spectra.TotalizationMilnor
