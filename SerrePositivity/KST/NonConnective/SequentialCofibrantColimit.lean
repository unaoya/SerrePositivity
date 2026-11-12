module

public import SerrePositivity.KST.NonConnective.SequentialRelativeHomFibration
public import SerrePositivity.KST.NonConnective.SequentialNativeHomLimit
public import SerrePositivity.KST.NonConnective.SequentialTowerIndex
public import SerrePositivity.KST.NonConnective.SequentialDiagramReplacement
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.StrictNativeCocones

/-!
概要：相対 cofibrant な逐次 BF 列の実際の ∞ 余極限。
方針：元の全反変 Hom の通常極限を、実 Kan fibration の塔として判定する。
規約：任意の列への適用では構成済みの置換列を使い、元の列への輸送は別に照合する。
使われ方：K-7 の同じ BF 候補を頂点とする実 Sp 余錐の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialCofibrantColimitSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialCofibrantColimitOppositeHomKan (X Y : OmegaSpectrum.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex Y.unop X.unop

/-- 相対 cofibrant な隣接射の全反変 Hom は、元の標準塔の各隣接射で Kan fibration。 -/
lemma sequentialNativeHomTower_fibration (D : SpectrumSequence.{u})
    (hD : ∀ n, IsSequentialRelativeCofibration (D.map (homOfLE (Nat.le_succ n))))
    (X : OmegaSpectrum.{u}ᵒᵖ) (n : ℕ) :
    Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (sequentialTowerIndex ⋙ D.op) X).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := by
  change Fibration (eHomWhiskerRight SSet (D.map (homOfLE (Nat.le_succ n))) X.unop)
  rw [← RawSpectrumMapping.pre_spectrum]
  exact sequentialRawHomPre_fibration _ (hD n) X.unop.toKanSequence

/-- 相対 cofibrant な逐次 BF 列の段ごとの実余錐は、元の Sp 図式上の ∞ 余極限。 -/
lemma sequentialLevelCocone_isColimit_of_relativeCofibrations (D : SpectrumSequence.{u})
    (hD : ∀ n, IsSequentialRelativeCofibration (D.map (homOfLE (Nat.le_succ n)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (sequentialLevelColimitCocone D)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_isLimit_iff_whisker (sequentialLevelColimitCocone D).op
    sequentialTowerIndex).mpr
  let : ∀ (X : OmegaSpectrum.{u}ᵒᵖ) (n : ℕ),
      Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (sequentialTowerIndex ⋙ D.op) X).map
        (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) :=
    fun X n ↦ sequentialNativeHomTower_fibration D hD X n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_tower_homLimit
  intro X
  exact (sequentialNativeHomIsLimit D X).whiskerEquivalence sequentialTowerIndexEquivalence

/-- 実置換図式の隣接射は、帰納構成した元の相対左因子に厳密に一致する。 -/
lemma sequentialDiagramReplacement_map_succ (D : SpectrumSequence.{u}) (n : ℕ) :
    (sequentialDiagramReplacement D).map (homOfLE (Nat.le_succ n)) =
      sequentialDiagramReplacementStep D n := by
  change (Functor.ofSequence (sequentialDiagramReplacementStep D)).map
    (homOfLE (Nat.le_succ n)) = _
  exact Functor.ofSequence_map_homOfLE_succ _ n

/-- 任意の元の逐次 BF 列から構成した置換図式の実余錐は、追加仮定なしの ∞ 余極限。 -/
lemma sequentialReplacementLevelCocone_isColimit (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone
      (sequentialLevelColimitCocone (sequentialDiagramReplacement D))) := by
  apply sequentialLevelCocone_isColimit_of_relativeCofibrations
  intro n
  rw [sequentialDiagramReplacement_map_succ]
  exact sequentialDiagramReplacementStep_isRelativeCofibration D n

end SerrePositivity.KST.NonConnective
