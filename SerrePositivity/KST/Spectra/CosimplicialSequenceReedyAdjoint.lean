module

public import SerrePositivity.KST.Spectra.ReedyPointedExtension
public import SerrePositivity.KST.Spectra.CosimplicialCotensorReedyKan
public import SerrePositivity.KST.Spectra.CosimplicialKanMapEquivalence
public import SerrePositivity.KST.Spectra.KanSequenceAdjointMap
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence

/-!
概要：余単体 Kan 列の Reedy 置換に、厳密に自然な随伴構造射を構成する。
方針：元の随伴構造と次段の置換単位を合成し、Reedy anodyne な単位に沿って延長する。
規約：延長先の loop 図式の Reedy Kan 性は内部 Hom の極限保存から証明済み。
使われ方：Goerss–Jardine VII §4、BF 1978 §2。Ω 図式の Reedy 置換。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 置換前の段の図式。 -/
abbrev originalLevel (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :=
  D ⋙ KanSequence.levelEvaluation n

/-- 置換後の段の図式。 -/
def level (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :=
  PointedCosimplicialKanReplacement.obj (originalLevel D n)

/-- 各段の Reedy anodyne な単位。 -/
def levelUnit (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    originalLevel D n ⟶ level D n :=
  PointedCosimplicialKanReplacement.unitApp _

/-- 元の図式の各段の Kan 性。 -/
instance originalLevel_kanComplex (D : CosimplicialObject KanSequence.{u})
    (n : ℕ) (j : SimplexCategory) : KanComplex ((originalLevel D n).obj j).right :=
  ((D.obj j).level n).kan

/-- 置換した図式の各段の Kan 性。 -/
instance level_kanComplex (D : CosimplicialObject KanSequence.{u})
    (n : ℕ) (j : SimplexCategory) : KanComplex ((level D n).obj j).right :=
  PointedCosimplicialKanReplacement.kanComplex _ _

/-- 置換した段は Reedy Kan 条件を満たす。 -/
lemma level_reedyTerminal (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (terminal.from (level D n ⋙ PointedSimplicialSet.forget)) :=
  CosimplicialKanReplacement.terminal_rlp _

/-- 元の随伴構造に次段の置換単位を合成した自然変換。 -/
def originalAdjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    originalLevel D n ⟶ level D (n + 1) ⋙ ihom PointedSimplicialSet.circle.{u} where
  app j := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((D.obj j).level n).space
      ((D.obj j).level (n + 1)).space ((D.obj j).sigma n) ≫
    (ihom PointedSimplicialSet.circle.{u}).map ((levelUnit D (n + 1)).app j)
  naturality i j f := by
    have h := (D.map f).adjoint_comm n
    change (D.map f).app n ≫ curry ((D.obj j).sigma n) =
      curry ((D.obj i).sigma n) ≫
        (ihom PointedSimplicialSet.circle.{u}).map ((D.map f).app (n + 1)) at h
    change (D.map f).app n ≫ curry ((D.obj j).sigma n) ≫ _ =
      (curry ((D.obj i).sigma n) ≫ _) ≫ _
    have hn := (levelUnit D (n + 1)).naturality f
    change (D.map f).app (n + 1) ≫ (levelUnit D (n + 1)).app j =
      (levelUnit D (n + 1)).app i ≫ (level D (n + 1)).map f at hn
    rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, hn,
      Functor.map_comp, Category.assoc]
    rfl

/-- Reedy Kan な loop 図式への延長の存在。 -/
lemma exists_adjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    ∃ b : level D n ⟶ level D (n + 1) ⋙ ihom PointedSimplicialSet.circle.{u},
      levelUnit D n ≫ b = originalAdjoint D n :=
  ReedyPointedExtension.exists_extension (levelUnit D n)
    (CosimplicialKanReplacement.unit_reedy_anodyne _)
    (CosimplicialCotensorReedyKan.reedyTerminal _ _ (level_reedyTerminal D (n + 1))) _

/-- 選択した厳密に自然な随伴構造。 -/
def adjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    level D n ⟶ level D (n + 1) ⋙ ihom PointedSimplicialSet.circle.{u} :=
  (exists_adjoint D n).choose

/-- 置換単位は随伴構造と厳密に可換する。 -/
lemma levelUnit_adjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    levelUnit D n ≫ adjoint D n = originalAdjoint D n :=
  (exists_adjoint D n).choose_spec

end
end SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
