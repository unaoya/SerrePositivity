module
public import SerrePositivity.KST.SConstruction.KSpectrumMaps
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-! # 実際の BF K スペクトルの整数ホモトピー群の関手
概要：全整数次数の K 群を構成済みの BF スペクトルから定義し、完全関手について関手化する。
方針：スペクトルの実際の射が誘導する群準同型へ、全段のホモトピー成分の法則を移す。
規約：値域は乗法記法の可換群。スペクトル値の coherent 関手性は別工程。
使われ方：π₀ K と K₀ の自然な群同型、dg への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- BF K スペクトルの射が実際の整数ホモトピー群に誘導する群準同型。 -/
def kHomotopyMap {X Y : StableModel.{u}} (f : X ⟶ Y) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j →*
      OmegaSpectrum.homotopyGroup (kOmegaSpectrum Y) j :=
  OmegaSpectrum.homotopyMap (kSpectrumMap f) j

/-- K の整数次数の誘導準同型は恒等完全関手を保つ。 -/
lemma kHomotopyMap_id (X : StableModel.{u}) (j : ℤ) :
    kHomotopyMap (𝟙 X) j = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro a
  rw [kHomotopyMap, OmegaSpectrum.homotopyMap_apply]
  change pointedHomotopyMap _ ((monicKKanSequenceMap (𝟙 X)).app _) a = a
  rw [pointedHomotopyMap_eq_of_component
    (monicKKanSequenceMap_id_component X (OmegaSpectrum.canonicalLevel j))]
  exact pointedHomotopyMap_id _ _ a

/-- K の整数次数の誘導準同型は完全関手の合成を保つ。 -/
lemma kHomotopyMap_comp {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (j : ℤ) :
    kHomotopyMap (f ≫ g) j = (kHomotopyMap g j).comp (kHomotopyMap f j) := by
  apply MonoidHom.ext
  intro a
  simp only [kHomotopyMap, OmegaSpectrum.homotopyMap_apply, MonoidHom.comp_apply]
  change pointedHomotopyMap _ ((monicKKanSequenceMap (f ≫ g)).app _) a =
    pointedHomotopyMap _ ((monicKKanSequenceMap g).app _)
      (pointedHomotopyMap _ ((monicKKanSequenceMap f).app _) a)
  rw [pointedHomotopyMap_eq_of_component
    (monicKKanSequenceMap_comp_component f g (OmegaSpectrum.canonicalLevel j))]
  exact pointedHomotopyMap_comp _ _ _ a

/-- 構成済みの連結 BF K スペクトルの整数次数の可換群への関手。 -/
def kHomotopyFunctor (j : ℤ) : StableModel.{u} ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j)
  map f := CommGrpCat.ofHom (kHomotopyMap f j)
  map_id X := congrArg CommGrpCat.ofHom (kHomotopyMap_id X j)
  map_comp f g := congrArg CommGrpCat.ofHom (kHomotopyMap_comp f g j)

end SerrePositivity.KST.SConstruction
