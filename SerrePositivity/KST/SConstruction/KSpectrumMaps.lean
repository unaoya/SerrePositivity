module
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum
public import SerrePositivity.KST.SConstruction.KSequenceMapLaws
public import SerrePositivity.KST.Spectra.SpectrumMorphisms

/-! # 完全関手からの実際の BF K スペクトルの射
概要：既存の単射置換の厳密な列の射を、構成済みの BF K スペクトルの射に束ねる。
方針：全段の射と構造射との厳密可換性を保ち、恒等・合成の成分の法則を移す。
規約：成分の法則を厳密な関手法則の代用にしない。使われ方：整数次数の K 群の関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra.PointedMapping

/-- 元の完全関手から構成した、同じ BF K 模型間の実際のスペクトルの射。 -/
def kSpectrumMap {X Y : StableModel.{u}} (f : X ⟶ Y) : kOmegaSpectrum X ⟶ kOmegaSpectrum Y where
  app := (monicKKanSequenceMap f).app
  comm := (monicKKanSequenceMap f).comm

/-- スペクトルの射の各成分は元の単射置換した列の射を保つ。 -/
lemma kSpectrumMap_app {X Y : StableModel.{u}} (f : X ⟶ Y) (r : ℕ) :
    (kSpectrumMap f).app r = (monicKKanSequenceMap f).app r := rfl

/-- 恒等関手のスペクトルの射は全段で恒等射と同じ点つきホモトピー成分。 -/
lemma kSpectrumMap_id_component (X : StableModel.{u}) (r : ℕ) :
    componentOf ((kSpectrumMap (𝟙 X)).app r) =
      componentOf (𝟙 (((kOmegaSpectrum X).level r).space)) := by
  rw [kSpectrumMap_app]
  exact monicKKanSequenceMap_id_component X r

end SerrePositivity.KST.SConstruction
