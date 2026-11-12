module

public import Mathlib.Algebra.Category.Grp.Zero
public import SerrePositivity.KST.ProExcision.Pro
public import SerrePositivity.KST.LocalizingInvariants.StableValueFunctor
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor

/-!
概要：局所化不変量の値の塔と、全整数次数の pro 同値・pro 零性の最小形式。
方針：既存の Tower・LevelHom・Artin–Mazur 判定を実 h Sp と整数 π 関手へ適用する。
規約：次数ごとの pro 判定。一般 pro ∞ 圏の零対象性とは同一視しない。
使われ方：d8 の pro 版と Tor の pro 消滅からの抽象切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.ProSpectrum
open ProExcision

instance commGroupZeroMorphisms : CategoryTheory.Limits.HasZeroMorphisms CommGrpCat.{u} :=
  (CommGrpCat.isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).hasZeroMorphisms

abbrev Tower := ProExcision.Tower (hoFunctor.obj Sp.{u})
abbrev LevelHom (X Y : Tower.{u}) := ProExcision.LevelHom X Y

def groups (X : Tower.{u}) (j : ℤ) : ProExcision.Tower CommGrpCat.{u} :=
  X.map (SpectrumHo.piFunctor j)

def IsPiProZero (X : Tower.{u}) : Prop := ∀ j : ℤ, IsProZero (groups X j)

def IsPiProEquivalence {X Y : Tower.{u}} (f : LevelHom X Y) : Prop :=
  ProExcision.IsProEquivalence (fun j : ℤ => SpectrumHo.piFunctor j) f

lemma piProEquivalence_of_proIso {X Y : Tower.{u}} {f : LevelHom X Y}
    (hf : IsProIso f) : IsPiProEquivalence f := fun j => hf.map (SpectrumHo.piFunctor j)

lemma levelHom_ext {C : Type v} [Category.{w} C] {X Y : ProExcision.Tower C}
    {f g : ProExcision.LevelHom X Y}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

lemma piProEquivalence_comp {X Y Z : Tower.{u}} {f : LevelHom X Y} {g : LevelHom Y Z}
    (hf : IsPiProEquivalence f) (hg : IsPiProEquivalence g) :
    IsPiProEquivalence (f.comp g) := by
  intro j
  have he : (f.comp g).map (SpectrumHo.piFunctor j) =
      (f.map (SpectrumHo.piFunctor j)).comp (g.map (SpectrumHo.piFunctor j)) := by
    apply levelHom_ext
    intro n
    exact (SpectrumHo.piFunctor j).map_comp (f.app n) (g.app n)
  rw [he]
  exact (hf j).comp (hg j)

lemma piProZero_of_levelwiseIso {X Y : Tower.{u}} (f : LevelHom X Y)
    [∀ n, IsIso (f.app n)] (hX : IsPiProZero X) : IsPiProZero Y := by
  intro j
  have (n : ℕ) : IsIso ((f.map (SpectrumHo.piFunctor j)).app n) := by
    change IsIso ((SpectrumHo.piFunctor j).map (f.app n))
    infer_instance
  exact IsProZero.of_levelwiseIso (f.map (SpectrumHo.piFunctor j)) (hX j)

end SerrePositivity.KST.LocalizingInvariants.ProSpectrum

namespace SerrePositivity.KST.LocalizingInvariants.ProValue
open ProExcision
variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u})

def tower (A : Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : ProSpectrum.Tower.{u} :=
  A.map (stableValueFunctor Φ)

def map {A B : Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : LevelHom A B) :
    ProSpectrum.LevelHom (tower Φ A) (tower Φ B) := f.map (stableValueFunctor Φ)

def IsPiProZero (A : Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : Prop := ProSpectrum.IsPiProZero (tower Φ A)

def IsPiProEquivalence {A B : Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (f : LevelHom A B) : Prop :=
  ProSpectrum.IsPiProEquivalence (map Φ f)

lemma piProEquivalence_of_proIso {A B : Tower _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {f : LevelHom A B}
    (hf : IsProIso f) : IsPiProEquivalence Φ f :=
  ProSpectrum.piProEquivalence_of_proIso (hf.map (stableValueFunctor Φ))

end SerrePositivity.KST.LocalizingInvariants.ProValue
