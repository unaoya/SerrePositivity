module
public import SerrePositivity.KST.NonConnective.FilteredExchangeLevelColimit
public import SerrePositivity.KST.NonConnective.SequentialLevelColimitFunctor
public import SerrePositivity.KST.NonConnective.SequentialCandidateMap
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：filtered な実逐次 BF 図式で、二通りの段別余極限を交換して元の BF 候補へ戻す。
方針：通常 BF 余極限の交換を元の普遍射で作り、同じ BF 射影へ持ち上げる。
規約：全入力 dg 作用・段別保存や一般 filtered Sp ∞ 余極限性は主張しない。
使われ方：K-7 e の filtered 保存で必要な、実 BF 実現の交換部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance exchangeSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable {J : Type u} [SmallCategory J] [IsFiltered J]

local instance exchangeFilteredColimits : HasColimitsOfShape J OmegaSpectrum.{u} where
  has_colimit E := ⟨_, FilteredExchange.levelColimitIsColimit E⟩

variable (D : J ⥤ SpectrumSequence.{u}) (c : Cocone D) (hc : IsColimit c)

/-- 各行を同じ元の段別逐次 BF 余極限で実現した、外側の厳密 filtered 図式。 -/
def sequentialFilteredLevelDiagram : J ⥤ OmegaSpectrum.{u} :=
  D ⋙ sequentialLevelColimitFunctor

/-- 元の外側余錐を、同じ厳密な逐次 BF 実現で送った実余錐。 -/
def sequentialFilteredLevelCocone : Cocone (sequentialFilteredLevelDiagram D) :=
  sequentialLevelColimitFunctor.mapCocone c

/-- 同じ外側余錐は、通常 BF 圏の余極限である。 -/
def sequentialFilteredLevelCocone_isColimit :
    IsColimit (sequentialFilteredLevelCocone D c) :=
  isColimitOfPreserves sequentialLevelColimitFunctor hc

/-- 二通りの実段別 BF 余極限の交換は、元の全注入を保つ一意同型。 -/
def sequentialFilteredLevelExchangeIso :
    FilteredExchange.levelColimitSpectrum (sequentialFilteredLevelDiagram D) ≅
      sequentialLevelColimitSpectrum (c.pt) :=
  (FilteredExchange.levelColimitIsColimit
    (sequentialFilteredLevelDiagram D)).coconePointUniqueUpToIso
    (sequentialFilteredLevelCocone_isColimit D c hc)

/-- 同じ交換同型は、元の外側注入を元の逐次比較へ厳密に送る。 -/
theorem sequentialFilteredLevelExchangeIso_injection (a : J) :
    FilteredExchange.levelColimitInjection (sequentialFilteredLevelDiagram D) a ≫
        (sequentialFilteredLevelExchangeIso D c hc).hom =
      sequentialLevelColimitMap (c.ι.app a) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (FilteredExchange.levelColimitIsColimit (sequentialFilteredLevelDiagram D))
    (sequentialFilteredLevelCocone_isColimit D c hc) a

/-- 元の外側 filtered BF 候補から、交換後の置換前逐次 BF 対象への実比較。 -/
def sequentialFilteredExchangeRawMap :
    OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D) ⟶
      sequentialLevelColimitSpectrum (c.pt) :=
  FilteredExchange.replacementProjection (sequentialFilteredLevelDiagram D) ≫
    (sequentialFilteredLevelExchangeIso D c hc).hom

/-- 元の交換比較を、同じ逐次 BF 候補の実射影へ持ち上げた実 BF 射。 -/
def sequentialFilteredExchangeMap :
    OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D) ⟶
      sequentialSpectrum (c.pt) := by
  let f := KanSequence.liftHom
    (X := (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D)).toKanSequence)
    (W := (sequentialSpectrum c.pt).toKanSequence)
    (Z := OmegaSpectrum.filteredKanSequence c.pt)
    (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D)).sigma_mono
    (OmegaSpectrum.filteredSequenceComparison (c.pt))
    (fun k => (KanSequence.replacementStage
      (OmegaSpectrum.filteredKanSequence (c.pt)) k).projection_rlp)
    (OmegaSpectrum.sequenceHom (sequentialFilteredExchangeRawMap D c hc))
  exact { app := f.app, comm := f.comm }

/-- 実 BF 交換射は同じ元の射影の下で厳密に可換する。 -/
theorem sequentialFilteredExchangeMap_projection :
    sequentialFilteredExchangeMap D c hc ≫ sequentialReplacementProjection (c.pt) =
      sequentialFilteredExchangeRawMap D c hc := by
  apply OmegaSpectrum.Hom.ext
  intro k
  exact KanSequence.liftHom_fac
    (X := (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D)).toKanSequence)
    (W := (sequentialSpectrum c.pt).toKanSequence)
    (Z := OmegaSpectrum.filteredKanSequence c.pt)
    (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D)).sigma_mono
    (OmegaSpectrum.filteredSequenceComparison (c.pt))
    (fun k => (KanSequence.replacementStage
      (OmegaSpectrum.filteredKanSequence (c.pt)) k).projection_rlp)
    (OmegaSpectrum.sequenceHom (sequentialFilteredExchangeRawMap D c hc)) k

/-- 同じ実 BF 交換射は、零段を含む全段・全基点の π 同型。 -/
theorem sequentialFilteredExchangeMap_levelwise (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((sequentialFilteredExchangeMap D c hc).app k).right := by
  let i :
      ((FilteredExchange.levelColimitSpectrum
        (sequentialFilteredLevelDiagram D)).level k).space.right ≅
        ((sequentialLevelColimitSpectrum c.pt).level k).space.right :=
    (OmegaSpectrum.levelEvaluation k ⋙ PointedSimplicialSet.forget).mapIso
      (sequentialFilteredLevelExchangeIso D c hc)
  have hr : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((sequentialFilteredExchangeRawMap D c hc).app k).right :=
    (OmegaSpectrum.filteredLevelComparison_piIsomorphism
      (sequentialFilteredLevelDiagram D) k).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso i)
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    (g := ((sequentialReplacementProjection c.pt).app k).right) _
    (OmegaSpectrum.filteredLevelComparison_piIsomorphism c.pt k)
  have h : ((sequentialFilteredExchangeMap D c hc).app k).right ≫
      ((sequentialReplacementProjection c.pt).app k).right =
        ((sequentialFilteredExchangeRawMap D c hc).app k).right :=
    congrArg (fun f => (f.app k).right) (sequentialFilteredExchangeMap_projection D c hc)
  rw [h]
  exact hr

/-- 同じ元の BF 交換射は全整数 π 同型。 -/
theorem sequentialFilteredExchangeMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (sequentialFilteredExchangeMap D c hc) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _ (sequentialFilteredExchangeMap_levelwise D c hc)

/-- 同じ実 BF 交換射の Sp 辺は可逆。一般 filtered Sp 余極限性とは区別する。 -/
theorem sequentialFilteredExchangeMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialFilteredExchangeMap D c hc)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _ (sequentialFilteredExchangeMap_piIsomorphism D c hc)

/-- 外側余極限の存在も構成済みなので、指定余錐を追加入力としない実交換射を得る。 -/
def sequentialFilteredCanonicalExchangeMap :
    OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D) ⟶
      sequentialSpectrum (colimit D) :=
  sequentialFilteredExchangeMap D (colimit.cocone D) (colimit.isColimit D)

/-- 同じ標準実交換射は、filtered/逐次 BF 図式だけから可逆な Sp 辺となる。 -/
theorem sequentialFilteredCanonicalExchangeMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialFilteredCanonicalExchangeMap D)) :=
  sequentialFilteredExchangeMap_isInvertible D (colimit.cocone D) (colimit.isColimit D)

end SerrePositivity.KST.NonConnective
