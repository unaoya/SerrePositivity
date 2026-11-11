module

public import SerrePositivity.KST.Spectra.SpectrumSimplicialCategory
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Quasicategory

/-!
概要：BF の cofibrant–fibrant な Ω スペクトルの coherent nerve。
方針：実証した単体的圏の局所 Kan 性に γ1 を適用する。
規約：導来写像空間を持つ正しい Sp との比較と ∞ 極限は γ3 後に扱う。
使われ方：HTT 1.1.5.10、HTT A.3.3、BF 1978 §2、HA §1.4.2。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.KST.Spectra

noncomputable section

local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

local instance (X Y : OmegaSpectrum.{u}) : SSet.KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 概要：BF 方式の Ω スペクトルの単体的圏の coherent nerve。
方針：Mathlib の SimplicialNerve を構成済みの単体的圏に適用する。
規約：第 1 段の Sp。導来写像空間との比較は γ3 後の工程。
使われ方：HTT 1.1.5.10、HTT A.3.3、BF 1978 §2、HA §1.4.2。 -/
def Sp := SimplicialNerve OmegaSpectrum.{u}

/-- 概要：Ω スペクトルの coherent nerve は quasicategory。
方針：写像空間の塔の相対充填から局所 Kan 性を得て γ1 を適用する。
規約：HT-KQ や安定モデル構造の存在は引用しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.1（Tag 00LJ）。KST の γ-B。 -/
instance sp_quasicategory : SSet.Quasicategory Sp.{u} := by
  dsimp only [Sp]
  infer_instance

end

end SerrePositivity.KST.Spectra
