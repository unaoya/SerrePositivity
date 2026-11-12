module

public import SerrePositivity.KST.Spectra.StandardEndOmegaCondition
public import SerrePositivity.KST.Spectra.KanSequenceLevelIso

/-!
概要：通常の点つき Tot そのものを各段に持つ Kan Ω 列と BK end への比較。
方針：標準単体 enriched end の構造を基点を保つ厳密同型で通常 Tot に移す。
規約：各段は置換前の通常 Tot。Reedy 条件は元の係数の各スペクトル次数に課す。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。通常 Tot の BF 模型の段の指定。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 余単体 Kan 列の通常 Tot そのものを各段に取る。 -/
def totalizationLevel (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (n : ℕ) : PointedKanComplex.{u} where
  space := PointedTotalization.obj (D ⋙ levelEvaluation n)
  kan := PointedTotalization.kanComplex (D ⋙ levelEvaluation n)
    ((CosimplicialHornFibration.terminal_iff _).mp (hD n))

/-- 標準単体 end から構造射を移した通常 Tot の実際の列。 -/
def totalizationKan (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) : KanSequence.{u} :=
  changeLevels (ordinaryTotalization D hD) (totalizationLevel D hD)
    (fun n ↦ PointedTotalization.standardEndIso (D ⋙ levelEvaluation n))

/-- 通常 Tot の列から標準単体 end の列への厳密な比較。 -/
def totalizationToStandard (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) : Hom (totalizationKan D hD) (ordinaryTotalization D hD) :=
  changeLevelsProjection _ _ _

/-- 通常 Tot の列は係数の Ω 条件を保つ。 -/
lemma totalizationKan_omegaCondition (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (hΩ : ∀ j, (D.obj j).OmegaCondition) :
    (totalizationKan D hD).OmegaCondition :=
  changeLevels_omegaCondition _ _ _ (ordinaryTotalization_omegaCondition D hD hΩ)

/-- 通常 Tot そのものの列から BK end の列への実際の構造可換射。 -/
def totalizationKanComparison (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) :
    Hom (totalizationKan D hD) (homotopyLimit (AsSmall.down ⋙ D)) :=
  (totalizationToStandard D hD).comp (totalizationComparison D hD)

/-- 列の比較の各段は、構成済みの通常 Tot の標準比較そのもの。 -/
lemma totalizationKanComparison_app (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (n : ℕ) :
    (totalizationKanComparison D hD).app n =
      PointedTotalization.weightedEndComparison (D ⋙ levelEvaluation n) := by
  exact (PointedTotalization.weightedEndComparison_eq_preMap
    (D ⋙ levelEvaluation n)).symm

/-- 通常 Tot の構造可換な標準比較は各段で全基点 π 同型。 -/
lemma totalizationKanComparison_levelwise (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((totalizationKanComparison D hD).app n).right := by
  rw [totalizationKanComparison_app]
  exact PointedTotalization.weightedEndComparison_piIsomorphism
    (D ⋙ levelEvaluation n) (hD n)

end
end SerrePositivity.KST.Spectra.KanSequence
