module
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor
public import SerrePositivity.KST.Spectra.StageComparisonNaturality

/-! # BF K 群の任意段表示の自然性
概要：全整数次数の K 群の基礎集合は、許される任意の段のホモトピー集合と自然同型。
方針：実際のスペクトルの射についての L9 の段比較の自然性を、既存の段の関手へ接続する。
規約：群と段は構成済みの BF 模型のものを使う。使われ方：π₀ と K₀ の自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 実際の整数 K 群から元の許される段への自然な表示。 -/
def kHomotopyStageIso (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    kHomotopyFunctor.{u} j ⋙ forget CommGrpCat.{u} ≅
      kStageHomotopyFunctor k (OmegaSpectrum.degree j k) :=
  NatIso.ofComponents
    (fun X => (OmegaSpectrum.homotopyGroupEquivAt (kOmegaSpectrum X) j k hk).toEquiv.toIso)
    (fun {X Y} f => by
      apply ConcreteCategory.hom_ext
      intro a
      change OmegaSpectrum.homotopyGroupEquivAt (kOmegaSpectrum Y) j k hk
        (kHomotopyMap f j a) =
        pointedHomotopyMap (OmegaSpectrum.degree j k) ((monicKKanSequenceMap f).app k)
          (OmegaSpectrum.homotopyGroupEquivAt (kOmegaSpectrum X) j k hk a)
      exact OmegaSpectrum.homotopyGroupEquivAt_natural (kSpectrumMap f) j k hk a)

/-- 実際の整数 K 群から単射置換前の元の段への自然な表示。 -/
def kHomotopyRawStageIso (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    kHomotopyFunctor.{u} j ⋙ forget CommGrpCat.{u} ≅
      rawKStageHomotopyFunctor k (OmegaSpectrum.degree j k) :=
  kHomotopyStageIso j k hk ≪≫ kStageHomotopyIso k (OmegaSpectrum.degree j k)

end SerrePositivity.KST.SConstruction
