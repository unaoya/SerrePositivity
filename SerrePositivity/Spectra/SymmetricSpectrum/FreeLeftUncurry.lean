module

public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleEvaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.Cotensor

/-! # 左自由因子の比較の下での逆転置とcotensorの逆比較 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet
open MonoidalModuleInternalHom (freeHomModuleIso freeHomIso)

/-- F_0との全体の逆比較の基礎射を、通常の内部Homの逆比較へ分解する。 -/
lemma internalHomCotensorIso_inv_hom (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorIso X E).inv.hom =
      (homBySequenceCotensorIso X E).inv ≫
        (freeHomModuleIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E).inv.hom := by
  rfl

/-- cotensorの逆比較を自由原変数の比較へ戻すと、移送の逆射になる。 -/
lemma internalHomCotensorIso_inv_freeHom (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorIso X E).inv.hom ≫
        (freeHomIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E).hom =
      (homBySequenceCotensorIso X E).inv := by
  have hinv :
      (freeHomModuleIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E).inv.hom =
        (freeHomIso sphereSequence.{u} ((SymmetricSequence.freeAt 0).obj X) E).inv := by
    as_aux_lemma =>
      rfl
  rw [internalHomCotensorIso_inv_hom, hinv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.SymmetricSpectrum
