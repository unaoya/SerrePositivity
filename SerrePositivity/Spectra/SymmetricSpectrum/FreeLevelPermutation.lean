module

public import SerrePositivity.Spectra.SymmetricSequence.FreePermutationAction
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelQuotientAction

/-! # 自由スペクトルの各段の対称群による誘導表示

n≤mの場合、Σ_mで添字付けたS^{m−n}とXのsmashの余積を、球面側の対称群の関係式で割る。
出力の左乗法と入力の射を含め、自由スペクトルの各段との自然同型を構成する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- Σ_mで添字付けた球面とXのsmashを、球面側のブロック作用の関係式で割った商。 -/
def freeAtLevelPermutationQuotient (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (hm : n ≤ m) : PointedSimplicialSet.{u} :=
  SymmetricSequence.freePermutationQuotient sphereSequence.{u} n X m hm

/-- 出力の置換τに対応する、誘導商の生成元。 -/
def freeAtLevelPermutationGenerator (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ)
    (hm : n ≤ m) (τ : Equiv.Perm (Fin m)) :
    spherePower.{u} (m - n) ⊗ X ⟶ freeAtLevelPermutationQuotient n X m hm :=
  SymmetricSequence.freePermutationQuotientGenerator sphereSequence.{u} n X m hm τ

/-- 誘導商の関係式は球面側の作用と、添字の右乗法を同一視する。 -/
@[reassoc] lemma freeAtLevelPermutationGenerator_relation (n : ℕ)
    (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : n ≤ m)
    (σ : Equiv.Perm (Fin (m - n))) (τ : Equiv.Perm (Fin m)) :
    (spherePermutationAction.{u} (m - n) σ).asIso.hom ▷ X ≫
        freeAtLevelPermutationGenerator n X m hm τ =
      freeAtLevelPermutationGenerator n X m hm
        (τ * SymmetricSequence.freeBlockPermutation n m hm σ) :=
  SymmetricSequence.freePermutationQuotientGenerator_relation sphereSequence.{u} n X m hm σ τ

/-- 自由スペクトルの第m段と、Σ_mで添字付けた誘導商との比較同型。 -/
def freeAtLevelIsoPermutation (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : n ≤ m) :
    level ((freeAt n).obj X) m ≅ freeAtLevelPermutationQuotient n X m hm :=
  freeAtLevelIsoBlockQuotient n X m ≪≫
    SymmetricSequence.freeBlockQuotientIsoPermutation sphereSequence.{u} n X m hm

/-- 比較同型は全単射の生成元を、対応する置換の生成元へ送る。 -/
@[reassoc] lemma freeAtLevelIsoPermutation_generator (n : ℕ)
    (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : n ≤ m)
    (h : SymmetricSequence.FreeBlockIndex n m) :
    freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) h ≫
        (freeAtLevelIsoPermutation n X m hm).hom =
      freeAtLevelPermutationGenerator n X m hm
        (SymmetricSequence.freePermutationIndex n m hm h) := by
  change freeAtLevelGenerator n X m (FiniteBijection.of (m - n)) h ≫
    (freeAtLevelIsoBlockQuotient n X m).hom ≫
      SymmetricSequence.freeBlockToPermutationQuotient sphereSequence.{u} n X m hm = _
  erw [GeneralSymmetricSpectrum.freeAtLevelIsoBlockQuotient_generator_assoc
    (K := circle.{u}) n X m h]
  exact SymmetricSequence.freeBlockToPermutationQuotient_generator sphereSequence.{u} n X m hm h

/-- 入力の射を同変射へ送る、Σ_mで添字付けた誘導商の関手。 -/
def freeAtLevelPermutationActionFunctor (n m : ℕ) (hm : n ≤ m) :
    PointedSimplicialSet.{u} ⥤ Action PointedSimplicialSet.{u} (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freePermutationActionFunctor sphereSequence.{u} n m hm

/-- 出力の対称群は誘導商の生成元の添字に左から掛ける。 -/
@[reassoc] lemma freeAtLevelPermutationGenerator_action (n : ℕ)
    (X : PointedSimplicialSet.{u}) (m : ℕ) (hm : n ≤ m) (κ τ : Equiv.Perm (Fin m)) :
    freeAtLevelPermutationGenerator n X m hm τ ≫
        (((freeAtLevelPermutationActionFunctor n m hm).obj X).ρ κ).asHom =
      freeAtLevelPermutationGenerator n X m hm (κ * τ) :=
  SymmetricSequence.freePermutationQuotientGenerator_output sphereSequence.{u} n X m hm κ τ

/-- 自由スペクトルの作用付き各段と、対称群の誘導商との自然同型。 -/
def freeAtLevelActionNatIsoPermutation (n m : ℕ) (hm : n ≤ m) :
    freeAt.{u} n ⋙ forget ⋙ SymmetricSequence.levelActionFunctor m ≅
      freeAtLevelPermutationActionFunctor n m hm :=
  freeAtLevelActionNatIsoBlockQuotient n m ≪≫
    SymmetricSequence.freeBlockActionNatIsoPermutation sphereSequence.{u} n m hm

/-- 入力の射は対称群の誘導商の各生成元のXの因子へ作用する。 -/
@[reassoc] lemma freeAtLevelPermutationGenerator_input (n : ℕ)
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) (m : ℕ) (hm : n ≤ m)
    (τ : Equiv.Perm (Fin m)) :
    freeAtLevelPermutationGenerator n X m hm τ ≫
        ((freeAtLevelPermutationActionFunctor n m hm).map f).hom =
      spherePower.{u} (m - n) ◁ f ≫ freeAtLevelPermutationGenerator n Y m hm τ :=
  SymmetricSequence.freePermutationQuotientGenerator_input sphereSequence.{u} n f m hm τ

/-- 作用付き自然同型は、基礎対象の誘導商への比較同型を持ち上げる。 -/
lemma freeAtLevelActionNatIsoPermutation_hom (n m : ℕ) (hm : n ≤ m)
    (X : PointedSimplicialSet.{u}) :
    ((freeAtLevelActionNatIsoPermutation n m hm).app X).hom.hom =
      (freeAtLevelIsoPermutation n X m hm).hom := rfl

end SerrePositivity.SymmetricSpectrum
