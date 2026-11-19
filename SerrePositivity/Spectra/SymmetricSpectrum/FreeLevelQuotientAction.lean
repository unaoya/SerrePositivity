module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotientAction
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelQuotient

/-! # 自由スペクトルの各段の作用付き商表示

明示的な余等化子上に出力の対称群を作用させ、入力の射を同変射へ送る。
自由スペクトルの各段および誘導図式との比較を自然同型として公開する。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (levelMap)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由スペクトルの明示的な商表示上の、出力の対称群作用。 -/
def freeAtLevelBlockAction (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    Action PointedSimplicialSet.{u} (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freeBlockQuotientAction sphereSequence.{u} n X m

/-- 入力の射を同変射へ送る、作用付き商表示の関手。 -/
def freeAtLevelBlockActionFunctor (n m : ℕ) :
    PointedSimplicialSet.{u} ⥤ Action PointedSimplicialSet.{u} (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freeBlockQuotientActionFunctor sphereSequence.{u} n m

/-- 商の生成元への置換作用は全単射の添字への後合成。 -/
@[reassoc] lemma freeAtLevelBlockGenerator_action (n : ℕ) (X : PointedSimplicialSet.{u})
    (m : ℕ) (σ : Equiv.Perm (Fin m)) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelBlockGenerator n X m h ≫ ((freeAtLevelBlockAction n X m).ρ σ).asHom =
      freeAtLevelBlockGenerator n X m (h ≫ FiniteBijection.permutation m σ) :=
  SymmetricSequence.freeBlockQuotientAction_generator sphereSequence.{u} n X m σ h

/-- 入力の射は商の各生成元のXの因子へ作用する。 -/
@[reassoc] lemma freeAtLevelBlockGenerator_input (n : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (m : ℕ) (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelBlockGenerator n X m h ≫ ((freeAtLevelBlockActionFunctor n m).map f).hom =
      spherePower.{u} (m - n) ◁ f ≫ freeAtLevelBlockGenerator n Y m h :=
  SymmetricSequence.freeBlockQuotientGenerator_input sphereSequence.{u} n f m h

/-- 自由スペクトルの各段と明示的な商との、対称群作用を備えた比較同型。 -/
def freeAtLevelActionIsoBlockQuotient (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    SymmetricSequence.levelAction ((freeAt n).obj X).X m ≅ freeAtLevelBlockAction n X m :=
  SymmetricSequence.freeConvolutionLevelActionIsoBlockQuotient sphereSequence.{u} n X m

/-- 各段と商との比較同型は入力の射に関して自然。 -/
@[reassoc] lemma freeAtLevelIsoBlockQuotient_input (n : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (m : ℕ) :
    levelMap ((freeAt n).map f) m ≫ (freeAtLevelIsoBlockQuotient n Y m).hom =
      (freeAtLevelIsoBlockQuotient n X m).hom ≫
        ((freeAtLevelBlockActionFunctor n m).map f).hom := by
  change ((freeAt n).map f).hom.app (FiniteBijection.of m) ≫ _ = _
  rw [freeAt_map_underlying]
  exact SymmetricSequence.freeConvolutionLevelIsoBlockQuotient_input sphereSequence.{u} n f m

/-- 自由スペクトルの作用付き各段と明示的な商表示との自然同型。 -/
def freeAtLevelActionNatIsoBlockQuotient (n m : ℕ) :
    freeAt.{u} n ⋙ forget ⋙ SymmetricSequence.levelActionFunctor m ≅
      freeAtLevelBlockActionFunctor n m :=
  NatIso.ofComponents (fun X => freeAtLevelActionIsoBlockQuotient n X m) (by
    intro X Y f
    apply Action.hom_ext
    exact freeAtLevelIsoBlockQuotient_input n f m)

/-- 作用付き商表示と、既存の作用付き誘導表示との自然同型。 -/
def freeAtLevelBlockActionNatIsoInduction (n m : ℕ) :
    freeAtLevelBlockActionFunctor.{u} n m ≅ freeAtLevelInductionActionFunctor n m :=
  SymmetricSequence.freeBlockQuotientActionNatIsoInduction sphereSequence.{u} n m

/-- 商と誘導表示の自然同型は、既存の基礎対象の比較同型を持ち上げる。 -/
lemma freeAtLevelBlockActionNatIsoInduction_hom (n m : ℕ) (X : PointedSimplicialSet.{u}) :
    ((freeAtLevelBlockActionNatIsoInduction n m).app X).hom.hom =
      (GeneralSymmetricSpectrum.freeAtLevelBlockQuotientIsoInduction (K := circle.{u}) n X m).hom :=
  SymmetricSequence.freeBlockQuotientActionIsoInduction_hom sphereSequence.{u} n X m

/-- 商を経由した作用付き自然同型は、元の誘導表示との自然同型に一致する。 -/
lemma freeAtLevelActionNatIsoBlockQuotient_trans (n m : ℕ) :
    freeAtLevelActionNatIsoBlockQuotient.{u} n m ≪≫ freeAtLevelBlockActionNatIsoInduction n m =
      freeAtLevelActionNatIsoInduction n m := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact congrArg Iso.hom
    (SymmetricSequence.freeConvolutionLevelActionIsoBlockQuotient_trans sphereSequence.{u} n X m)

end SerrePositivity.SymmetricSpectrum
