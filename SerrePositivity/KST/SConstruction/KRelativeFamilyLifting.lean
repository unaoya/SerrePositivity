module
public import SerrePositivity.KST.SConstruction.RelativeSequenceFamilyRectification
public import SerrePositivity.KST.SConstruction.MonicKSequenceMaps
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum
public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic

/-! # 元の K の単射置換への全パラメータ族の相対持ち上げ
概要：元の列への厳密化した族を、指定境界を保って実際の BF K の写像空間へ持ち上げる。
方針：元の単射置換の射影の全単射 RLP を実写像空間に移して使う。
規約：元の BF K と元の列への射影を固定し、全段の評価の厳密な式を保持する。
使われ方：パラメータ付き厳密化と単射置換を合わせた、K の coherent 関手化の充填工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 元の BF K の全写像空間から、元の未置換列への写像空間への実際の射影。 -/
def kRawMappingProjection (X Y : StableModel.{u}) :
    OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) ⟶
      RawSpectrumMapping.space (kOmegaSpectrum X) (kKanSequence Y) :=
  RawSpectrumMapping.post (kOmegaSpectrum X) (monicKKanSequenceProjection Y)

/-- 元の単射置換の射影は、全写像空間で全てのパラメータ単射を持ち上げる。 -/
lemma kRawMappingProjection_rlp (X Y : StableModel.{u}) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (kRawMappingProjection X Y) :=
  RawSpectrumMapping.post_rlp (kOmegaSpectrum X) (monicKKanSequenceProjection Y)
    (monicKKanSequenceProjection_rlp Y)

/-- 全写像空間の射影は、各段で元の単射置換の射影による後合成そのもの。 -/
lemma kRawMappingProjection_evaluation (X Y : StableModel.{u}) (n : ℕ) :
    kRawMappingProjection X Y ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum X) (kKanSequence Y) n =
      OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
          ((monicKKanSequenceProjection Y).app n)).right :=
  RawSpectrumMapping.post_evaluation (kOmegaSpectrum X) (monicKKanSequenceProjection Y) n

/-- 元の射影に沿って、全パラメータと指定境界を保つ実際の BF 写像族を得る。 -/
def kRelativeFamilyLiftData (X Y : StableModel.{u}) {T U : SSet.{u}}
    (j : T ⟶ U) [Mono j]
    (a : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
    (b : U ⟶ RawSpectrumMapping.space (kOmegaSpectrum X) (kKanSequence Y))
    (h : a ≫ kRawMappingProjection X Y = j ≫ b) :
    {l : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      j ≫ l = a ∧ l ≫ kRawMappingProjection X Y = b} := by
  let : HasLiftingProperty j (kRawMappingProjection X Y) :=
    kRawMappingProjection_rlp X Y j inferInstance
  let sq : CommSq a j (kRawMappingProjection X Y) b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 持ち上げた族は、全段で元の未置換列の指定した族を回収する。 -/
lemma kRelativeFamilyLiftData_evaluation (X Y : StableModel.{u}) {T U : SSet.{u}}
    (j : T ⟶ U) [Mono j]
    (a : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
    (b : U ⟶ RawSpectrumMapping.space (kOmegaSpectrum X) (kKanSequence Y))
    (h : a ≫ kRawMappingProjection X Y = j ≫ b) (n : ℕ) :
    (kRelativeFamilyLiftData X Y j a b h).val ≫
      OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
          ((monicKKanSequenceProjection Y).app n)).right =
      b ≫ RawSpectrumMapping.evaluation (kOmegaSpectrum X) (kKanSequence Y) n := by
  rw [← kRawMappingProjection_evaluation, ← Category.assoc,
    (kRelativeFamilyLiftData X Y j a b h).property.2]

end SerrePositivity.KST.SConstruction
