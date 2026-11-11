module

public import SerrePositivity.KST.Spectra.SpectrumPointLoopReference
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPointed
public import SerrePositivity.KST.Spectra.LoopCircleBousfieldKanComparison

/-!
概要：一点 → Y ← 一点の実際のスペクトル Hom 図式を、零係数 cospan へ同定する。
方針：両端の Hom の終対象性と、元の後合成が零写像を保つことを使う。
規約：中央の Hom は恒等同型に固定する。使われ方：円評価錐の元の BK end への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance pointLoopCoefficientSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 一点からの射への豊穣後合成は、元の Hom の零写像で定数となる。 -/
lemma pointLoopHomLeg_eq_const (X Y : OmegaSpectrum.{u}) :
    ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map
        (fromPoint Y) =
      SSet.const (RawSpectrumMapping.pointedSpace X Y.toKanSequence).basepoint := by
  let p : KanSequence.Hom _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence Y.toKanSequence :=
    ⟨(fromPoint Y).app, (fromPoint Y).comm⟩
  have baseIso : IsIso (RawSpectrumMapping.pointedSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom :=
    isIso_of_isTerminal isTerminalTensorUnit (mappingPoint_isTerminal X) _
  rw [← RawSpectrumMapping.post_spectrum]
  calc
    RawSpectrumMapping.post X p =
        toUnit _ ≫ (RawSpectrumMapping.pointedSpace X Y.toKanSequence).hom := by
      apply (cancel_epi (RawSpectrumMapping.pointedSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom).mp
      have hu : (RawSpectrumMapping.pointedSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.toKanSequence).hom ≫
          toUnit _ = 𝟙 (𝟙_ SSet.{u}) := isTerminalTensorUnit.hom_ext _ _
      rw [← Category.assoc]
      erw [hu, Category.id_comp]
      exact Under.w (RawSpectrumMapping.pointedPost X p)
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const _ _

/-- 一点への Hom は、標準零単体と厳密に同型。 -/
def pointLoopHomEndpointIso (X : OmegaSpectrum.{u}) :
    mappingSpace X _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint ≅ (Δ[0] : SSet.{u}) :=
  (mappingPoint_isTerminal X).uniqueUpToIso stdSimplex.isTerminalObj₀

/-- 実際の Hom cospan の各成分を、両端は一点、中央は元の Hom として表示する。 -/
def pointLoopHomCoefficientComponent (X Y : OmegaSpectrum.{u})
    (i : AsSmall.{u} WalkingCospan) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X).obj i ≅
      (loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).obj i :=
  match i with
  | ⟨none⟩ => Iso.refl _
  | ⟨some .left⟩ => pointLoopHomEndpointIso X
  | ⟨some .right⟩ => pointLoopHomEndpointIso X

/-- 元の固定図式のスペクトル Hom は、中央を恒等に保って零係数 cospan と自然同型。 -/
def pointLoopHomCoefficientIso (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X ≅
      loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence) :=
  NatIso.ofComponents (pointLoopHomCoefficientComponent X Y) (by
    rintro ⟨a⟩ ⟨b⟩ ⟨f⟩
    change WidePullbackShape.Hom a b at f
    cases f with
    | id a =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X).map (𝟙 (AsSmall.up.obj a)) ≫ _ =
        _ ≫ (loopCoefficient (RawSpectrumMapping.pointedSpace X Y.toKanSequence)).map (𝟙 _)
      simp
    | term k =>
      cases k <;>
        change ((SimplicialCategory.sHomFunctor OmegaSpectrum.{u}).obj (Opposite.op X)).map
          (fromPoint Y) ≫ 𝟙 _ = _ ≫ SSet.const _
      all_goals rw [Category.comp_id, SSet.comp_const, pointLoopHomLeg_eq_const])

/-- 中央の Hom の成分は、構成した自然同型でも元の恒等射のまま。 -/
lemma pointLoopHomCoefficientIso_central (X Y : OmegaSpectrum.{u}) :
    (pointLoopHomCoefficientIso X Y).hom.app (AsSmall.up.obj .one) =
      𝟙 (mappingSpace X Y) := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
