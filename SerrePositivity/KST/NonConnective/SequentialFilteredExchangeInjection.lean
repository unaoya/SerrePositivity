module
public import SerrePositivity.KST.NonConnective.SequentialFilteredExchange
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapPi

/-!
概要：実 filtered/逐次 BF 交換を、元の各行の非連結化候補と同じ実注入へ照合する。
方針：同じ射影の下で全注入を厳密比較し、可逆な射影を hSp で消去する。
規約：元の各候補・実 BF 射を保持。dg 入力作用や一般 filtered ∞ 余極限性は追加しない。
使われ方：K-7 e の実比較と元の候補群の filtered 余極限計算の接続。
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
local instance exchangeInjectionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (D : J ⥤ SpectrumSequence.{u}) (c : Cocone D) (hc : IsColimit c)

/-- 元の各行の同じ BF 候補から、外側 filtered BF 実現への実注入。 -/
def sequentialFilteredCandidateInjection (a : J) :
    sequentialSpectrum (D.obj a) ⟶
      OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D) :=
  sequentialReplacementProjection (D.obj a) ≫
    OmegaSpectrum.filteredSpectrumInjection (sequentialFilteredLevelDiagram D) a

/-- 同じ実行注入と実交換射は、元の射影の下で厳密に可換する。 -/
theorem sequentialFilteredCandidateInjection_projection (a : J) :
    sequentialFilteredCandidateInjection D a ≫ sequentialFilteredExchangeMap D c hc ≫
        sequentialReplacementProjection c.pt =
      sequentialReplacementProjection (D.obj a) ≫ sequentialLevelColimitMap (c.ι.app a) := by
  have h : OmegaSpectrum.filteredSpectrumInjection (sequentialFilteredLevelDiagram D) a ≫
      FilteredExchange.replacementProjection (sequentialFilteredLevelDiagram D) =
        FilteredExchange.levelColimitInjection (sequentialFilteredLevelDiagram D) a := by
    apply OmegaSpectrum.Hom.ext
    intro k
    exact OmegaSpectrum.filteredSpectrumInjection_comparison _ a k
  calc
    _ = sequentialReplacementProjection (D.obj a) ≫
        (OmegaSpectrum.filteredSpectrumInjection (sequentialFilteredLevelDiagram D) a ≫
          FilteredExchange.replacementProjection (sequentialFilteredLevelDiagram D)) ≫
        (sequentialFilteredLevelExchangeIso D c hc).hom := by
      simp only [sequentialFilteredCandidateInjection, Category.assoc,
        sequentialFilteredExchangeMap_projection, sequentialFilteredExchangeRawMap]
    _ = sequentialReplacementProjection (D.obj a) ≫
        FilteredExchange.levelColimitInjection (sequentialFilteredLevelDiagram D) a ≫
          (sequentialFilteredLevelExchangeIso D c hc).hom :=
      congrArg (fun f => sequentialReplacementProjection (D.obj a) ≫ f ≫
        (sequentialFilteredLevelExchangeIso D c hc).hom) h
    _ = _ := congrArg (sequentialReplacementProjection (D.obj a) ≫ ·)
      (sequentialFilteredLevelExchangeIso_injection D c hc a)

/-- 元の行注入を交換射へ続けると、同じ元の候補比較の hSp 類を回収する。 -/
theorem sequentialFilteredCandidateInjection_exchange (a : J) :
    SpectrumHo.hom (sequentialFilteredCandidateInjection D a) ≫
        SpectrumHo.hom (sequentialFilteredExchangeMap D c hc) =
      SpectrumHo.hom (sequentialCandidateMap (c.ι.app a)) := by
  have hp : IsIso (SpectrumHo.hom (sequentialReplacementProjection c.pt)) :=
    OmegaSpectrum.isInvertible_of_piIsomorphism _
      (sequentialReplacementProjection_piIsomorphism c.pt)
  apply (cancel_mono (SpectrumHo.hom (sequentialReplacementProjection c.pt))).mp
  rw [Category.assoc, ← SpectrumHo.hom_comp, ← SpectrumHo.hom_comp,
    sequentialFilteredCandidateInjection_projection, SpectrumHo.hom_comp]
  exact (sequentialCandidateMap_projection (c.ι.app a)).symm

/-- 同じ実行注入と交換射は、元の候補比較の全整数 π 作用を回収する。 -/
theorem sequentialFilteredCandidateInjection_pi (a : J) (j : ℤ) :
    (OmegaSpectrum.homotopyMap (sequentialFilteredExchangeMap D c hc) j).comp
        (OmegaSpectrum.homotopyMap (sequentialFilteredCandidateInjection D a) j) =
      OmegaSpectrum.homotopyMap (sequentialCandidateMap (c.ι.app a)) j := by
  have h := sequentialFilteredCandidateInjection_exchange D c hc a
  rw [← SpectrumHo.hom_comp] at h
  exact (OmegaSpectrum.homotopyMap_comp _ _ j).symm.trans
    (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ h j)

include c hc in
/-- 同じ元の候補注入は、元の逐次比較に対して hSp で自然である。 -/
theorem sequentialFilteredCandidateInjection_naturality {a b : J} (f : a ⟶ b) :
    sequentialCandidateHoMap (D.map f) ≫
        SpectrumHo.hom (sequentialFilteredCandidateInjection D b) =
      SpectrumHo.hom (sequentialFilteredCandidateInjection D a) := by
  have he : IsIso (SpectrumHo.hom (sequentialFilteredExchangeMap D c hc)) :=
    sequentialFilteredExchangeMap_isInvertible D c hc
  apply (cancel_mono (SpectrumHo.hom (sequentialFilteredExchangeMap D c hc))).mp
  rw [Category.assoc, sequentialFilteredCandidateInjection_exchange,
    sequentialFilteredCandidateInjection_exchange,
    sequentialCandidateMap_hom, sequentialCandidateMap_hom,
    ← sequentialCandidateHoMap_comp, c.w f]

/-- 元の各行の同じ候補を全脚とする実 hSp 余錐。∞ 余錐の供給とは区別する。 -/
def sequentialFilteredCandidateHoCocone : Cocone (D ⋙ sequentialCandidateHoFunctor) where
  pt := SpectrumHo.obj (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D))
  ι := {
    app a := SpectrumHo.hom (sequentialFilteredCandidateInjection D a)
    naturality _ _ f := sequentialFilteredCandidateInjection_naturality D c hc f }

/-- 同じ実 BF 交換射の類は、元の候補比較の余錐への射を与える。 -/
def sequentialFilteredExchangeHoCoconeMap :
    sequentialFilteredCandidateHoCocone D c hc ⟶ sequentialCandidateHoFunctor.mapCocone c where
  hom := SpectrumHo.hom (sequentialFilteredExchangeMap D c hc)
  w a := by
    change SpectrumHo.hom (sequentialFilteredCandidateInjection D a) ≫
      SpectrumHo.hom (sequentialFilteredExchangeMap D c hc) = sequentialCandidateHoMap (c.ι.app a)
    rw [sequentialFilteredCandidateInjection_exchange, sequentialCandidateMap_hom]

end SerrePositivity.KST.NonConnective
