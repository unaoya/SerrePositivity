module

public import SerrePositivity.Spectra.SymmetricSequence.SphereCommMonoid
public import Mathlib.CategoryTheory.Monoidal.Mod

/-! # 球面モノイド上の加群としての対称スペクトル

Mathlibの内部加群を再利用して、対象・射・圏と忘却関手を構成する。
レベル同値・安定同値・モデル構造はまだ含まない。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity
/-- 球面対称列のモノイド上の内部加群としての対称スペクトル。 -/
abbrev SymmetricSpectrum := Mod PointedSymmetricSequence.{u} PointedSimplicialSet.sphereSequence.{u}
namespace SymmetricSpectrum
open PointedSimplicialSet
/-- 対称スペクトルの underlying 対称列。 -/
abbrev underlying (E : SymmetricSpectrum.{u}) : PointedSymmetricSequence.{u} := E.X
/-- 球面の加群作用を忘れる関手。 -/
def forget : SymmetricSpectrum.{u} ⥤ PointedSymmetricSequence.{u} :=
  Mod.forget (D := PointedSymmetricSequence.{u}) sphereSequence.{u}
instance forget_faithful : (forget.{u}).Faithful where
  map_injective := fun h ↦ Mod.hom_ext _ _ h
/-- 対称スペクトルの第n段の基点付き単体的集合。 -/
abbrev level (E : SymmetricSpectrum.{u}) (n : ℕ) : PointedSimplicialSet.{u} :=
  SymmetricSequence.level E.X n
/-- convolutionによる球面対称列の加群作用。 -/
def action (E : SymmetricSpectrum.{u}) : sphereSequence.{u} ⊗ E.X ⟶ E.X :=
  ModObj.smul (M := sphereSequence.{u}) (X := E.X)
/-- 加群作用の単位則。 -/
lemma action_unit (E : SymmetricSpectrum.{u}) :
    sphereUnitHom.{u} ▷ E.X ≫ action E = (λ_ E.X).hom :=
  ModObj.one_smul_self sphereSequence.{u} E.X
/-- 加群作用の結合則。 -/
lemma action_assoc (E : SymmetricSpectrum.{u}) :
    sphereMultiplication.{u} ▷ E.X ≫ action E =
      (α_ sphereSequence.{u} sphereSequence.{u} E.X).hom ≫
        sphereSequence.{u} ◁ action E ≫ action E :=
  ModObj.mul_smul_self sphereSequence.{u} E.X
/-- スペクトルの射は球面の作用と両立する。 -/
@[reassoc] lemma action_hom {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    action E ≫ f.hom = sphereSequence.{u} ◁ f.hom ≫ action F :=
  IsModHom.smul_hom (A := sphereSequence.{u}) (f := f.hom)
/-- 対称列・作用・単位則・結合則から対称スペクトルを作る。 -/
def mk (F : PointedSymmetricSequence.{u}) (a : sphereSequence.{u} ⊗ F ⟶ F)
    (hu : sphereUnitHom.{u} ▷ F ≫ a = (λ_ F).hom)
    (ha : sphereMultiplication.{u} ▷ F ≫ a =
      (α_ sphereSequence.{u} sphereSequence.{u} F).hom ≫ sphereSequence.{u} ◁ a ≫ a) :
    SymmetricSpectrum.{u} :=
  letI : ModObj sphereSequence.{u} F := { smul := a, one_smul := hu, mul_smul := ha }
  ⟨F⟩
/-- 球面の作用と両立する対称列の射からスペクトルの射を作る。 -/
def homMk {E F : SymmetricSpectrum.{u}} (f : E.X ⟶ F.X)
    (h : action E ≫ f = sphereSequence.{u} ◁ f ≫ action F) : E ⟶ F :=
  Mod.Hom.mk' f h
/-- スペクトルの射の成分は、次数の等式による移送と両立する。 -/
lemma hom_index_eq {E F : SymmetricSpectrum.{u}} (f : E ⟶ F)
    {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (level E) h) ≫ f.hom.app (FiniteBijection.of n) =
      f.hom.app (FiniteBijection.of m) ≫ eqToHom (congrArg (level F) h) := by
  subst n
  simp

/-- スペクトルの射の第n段の成分。 -/
def levelMap {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (n : ℕ) : level E n ⟶ level F n :=
  f.hom.app (FiniteBijection.of n)

/-- 恒等射の各段の成分は恒等射。 -/
lemma levelMap_id (E : SymmetricSpectrum.{u}) (n : ℕ) : levelMap (𝟙 E) n = 𝟙 (level E n) := rfl

/-- 合成の各段の成分は成分の合成。 -/
lemma levelMap_comp {E F G : SymmetricSpectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) (n : ℕ) :
    levelMap (f ≫ g) n = levelMap f n ≫ levelMap g n := rfl

/-- スペクトルの射は各段の成分で決まる。 -/
lemma hom_ext {E F : SymmetricSpectrum.{u}} (f g : E ⟶ F)
    (h : ∀ n, levelMap f n = levelMap g n) : f = g := by
  apply Mod.hom_ext
  apply NatTrans.ext
  funext A
  rw [← FiniteBijection.of_card A]
  exact h (FiniteBijection.card A)

end SymmetricSpectrum
end SerrePositivity
