module

public import SerrePositivity.EInfinity.PowerOperation.KanSequenceReplacementFunctor
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Ω 列から既存 BF スペクトルへの全関手

BF 1978 §2 の逐次単射置換を Ω 条件を満たす列の充満部分圏に制限する。
対象ごとの新たな選択を行わず、実際の同じ段と構造射を保持する。
［一般∞］移動候補。Eilenberg–Mac Lane 列の Ω 条件自体は別途証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.KST.Spectra

/-- 全基点・零次数を含む既存の Ω 条件を満たす列の性質。 -/
def kanOmegaSequenceProperty : ObjectProperty KanSequence.{u} :=
  fun X => X.OmegaCondition

/-- Ω 列の充満部分圏。 -/
abbrev KanOmegaSequence := kanOmegaSequenceProperty.{u}.FullSubcategory

/-- 指定された既存の単射置換による、Ω 列の全関手。 -/
def omegaSequenceReplacementFunctor : KanOmegaSequence.{u} ⥤ OmegaSpectrum.{u} where
  obj X := X.obj.cofibrantOmegaSpectrum X.property
  map f := {
    app n := (kanSequenceReplacementMap f.hom).app n
    comm n := (kanSequenceReplacementMap f.hom).comm n }
  map_id X := by
    apply OmegaSpectrum.Hom.ext
    intro n
    exact replacementStageMap_id X.obj n
  map_comp f g := by
    apply OmegaSpectrum.Hom.ext
    intro n
    exact replacementStageMap_comp f.hom g.hom n

/-- 出力の各段は、既存の同じ逐次置換の段である。 -/
lemma omegaSequenceReplacementFunctor_level (X : KanOmegaSequence.{u}) (n : ℕ) :
    ((omegaSequenceReplacementFunctor.obj X).level n).space =
      (KanSequence.replacementStage X.obj n).level.space := rfl

/-- 元の列の段ごとの π 同型は出力の段ごとの π 同型となる。 -/
lemma omegaSequenceReplacementFunctor_piIsomorphism
    {X Y : KanOmegaSequence.{u}} (f : X ⟶ Y)
    (hf : ∀ n, SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (f.hom.app n).right) (n : ℕ) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (((omegaSequenceReplacementFunctor.map f).app n).right) :=
  kanSequenceReplacementMap_piIsomorphism f.hom hf n

end SerrePositivity.EInfinity.PowerOperation
