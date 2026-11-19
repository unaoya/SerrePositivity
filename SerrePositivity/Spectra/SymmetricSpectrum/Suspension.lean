module

public import SerrePositivity.Spectra.SymmetricSpectrum.StructureMaps

/-! # 対称スペクトルの懸垂構造射

第1段の構造射から、円と第n段のsmashを第n+1段へ送る射を取り出す。
右単位子による第1段の表示と次数の移送を明示する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (hom_index_eq level structureMap structureMap_hom)

open SerrePositivity.PointedSimplicialSet

/-- 円のsmashによる標準の懸垂構造射。 -/
def suspensionMap (E : SymmetricSpectrum.{u}) (n : ℕ) :
    PointedObject.smash (circle : PointedSimplicialSet.{u}) (level E n) ⟶ level E (n + 1) :=
  PointedObject.smashMap (spherePowerOneIso.{u}).inv (𝟙 (level E n)) ≫
    structureMap E 1 n ≫ eqToHom (congrArg (level E) (Nat.one_add n))
/-- スペクトルの射は懸垂構造射と両立する。 -/
lemma suspensionMap_hom {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (n : ℕ) :
    suspensionMap E n ≫ f.hom.app (FiniteBijection.of (n + 1)) =
      PointedObject.smashMap (𝟙 (circle : PointedSimplicialSet.{u}))
          (f.hom.app (FiniteBijection.of n)) ≫ suspensionMap F n := by
  have hc := hom_index_eq f (Nat.one_add n)
  have hs : structureMap E 1 n ≫ f.hom.app (FiniteBijection.of (1 + n)) =
      PointedObject.smashMap (𝟙 (spherePower 1)) (f.hom.app (FiniteBijection.of n)) ≫
        structureMap F 1 n := structureMap_hom f 1 n
  simp only [suspensionMap, Category.assoc]
  rw [hc]
  rw [← Category.assoc _ _ (eqToHom (congrArg (level F) (Nat.one_add n))), hs]
  simp only [Category.assoc]
  simp only [← Category.assoc, PointedObject.smashMap_comp, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

end SerrePositivity.SymmetricSpectrum
