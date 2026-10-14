module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomAction
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFreeLevels

/-! # F_nからの内部Homの各段の置換作用

第m段の置換は、比較の下で値域の第n+m段の後ろのm要素の置換へ対応する。
球面作用・構造射の具体式は後続の段階で扱う。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory

/-- F_nからの内部Homの第m段の置換は、値域の後ろのm要素の置換と両立する。 -/
@[reassoc]
lemma internalHomFreeAtLevelIso_permutation (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (σ : Equiv.Perm (Fin m)) :
    (internalHom ((freeAt n).obj X) E).X.map (FiniteBijection.permutation m σ) ≫
        (internalHomFreeAtLevelIso n m X E).hom =
      (internalHomFreeAtLevelIso n m X E).hom ≫ (ihom X).map
        (E.X.map (FiniteBijection.sumMap (𝟙 (FiniteBijection.of n))
          (FiniteBijection.permutation m σ))) := by
  change (internalHom ((freeAt n).obj X) E).X.map (FiniteBijection.permutation m σ) ≫
    (internalHomFreeAtIso n X E).hom.hom.app (FiniteBijection.of m) ≫
      (SymmetricSequence.freeInternalHomLevelIso n m X E.X).hom =
    ((internalHomFreeAtIso n X E).hom.hom.app (FiniteBijection.of m) ≫
      (SymmetricSequence.freeInternalHomLevelIso n m X E.X).hom) ≫ _
  rw [(internalHomFreeAtIso n X E).hom.hom.naturality_assoc]
  erw [SymmetricSequence.freeInternalHomLevelIso_permutation]
  simp only [Category.assoc]

/-- 各段の比較は対称群作用を持つ基点付き単体的集合の同型。 -/
def internalHomFreeAtLevelActionIso (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    SymmetricSequence.levelAction (internalHom ((freeAt n).obj X) E).X m ≅
      SymmetricSequence.levelAction (SymmetricSequence.shiftedInternalHom n X E.X) m :=
  Action.mkIso (internalHomFreeAtLevelIso n m X E)
    (fun σ => internalHomFreeAtLevelIso_permutation n m X E σ)

/-- 作用付き比較の基礎射は既存の各段の比較。 -/
lemma internalHomFreeAtLevelActionIso_hom (n m : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomFreeAtLevelActionIso n m X E).hom.hom =
      (internalHomFreeAtLevelIso n m X E).hom := rfl

end SerrePositivity.SymmetricSpectrum
