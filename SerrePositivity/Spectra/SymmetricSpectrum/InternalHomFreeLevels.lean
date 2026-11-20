module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHom
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFreeNaturality

/-! # F_nを原変数とする内部Homの各段

第m段を、生成元Xから値域スペクトルの第n+m段への基点付き内部Homへ比較する。
置換作用・球面作用の各段の具体式は後続の段階で整える。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 第n段の自由対称列からの通常の内部Homの第m段。 -/
def homBySequenceFreeAtLevelIso (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    level (homBySequence ((SymmetricSequence.freeAt n).obj X) E) m ≅
      (ihom X).obj (level E (n + m)) :=
  SymmetricSequence.freeInternalHomLevelIso (C := PointedSimplicialSet.{u}) n m X E.X

/-- F_nを原変数とする内部Homの第m段と、第n+m段への基点付き内部Homの比較。 -/
def internalHomFreeAtLevelIso (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    level (internalHom ((freeAt n).obj X) E) m ≅ (ihom X).obj (level E (n + m)) :=
  (evaluation m).mapIso (internalHomFreeAtIso n X E) ≪≫ homBySequenceFreeAtLevelIso n m X E

/-- 各段の比較は、自由原変数の比較と通常の内部Homの各段の比較の合成。 -/
lemma internalHomFreeAtLevelIso_eq (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    internalHomFreeAtLevelIso n m X E =
      (evaluation m).mapIso (internalHomFreeAtIso n X E) ≪≫
        homBySequenceFreeAtLevelIso n m X E := rfl

/-- 内部Homの各段への射は第n+m段への内部Homへの射と同値。 -/
def internalHomFreeAtLevelHomEquiv (n m : ℕ) (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (Y ⟶ level (internalHom ((freeAt n).obj X) E) m) ≃
      (Y ⟶ (ihom X).obj (level E (n + m))) where
  toFun f := f ≫ (internalHomFreeAtLevelIso n m X E).hom
  invFun f := f ≫ (internalHomFreeAtLevelIso n m X E).inv
  left_inv f := by simp
  right_inv f := by simp

/-- 第零段ではF_nからの内部Homが第n段への基点付き内部Homになる。 -/
def internalHomFreeAtLevelZeroIso (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    level (internalHom ((freeAt n).obj X) E) 0 ≅ (ihom X).obj (level E n) := by
  simpa only [Nat.add_zero] using internalHomFreeAtLevelIso n 0 X E

end SerrePositivity.SymmetricSpectrum
