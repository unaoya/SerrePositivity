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

/-- 左自由因子の比較の下でのスペクトルの逆転置。 -/
lemma sphereTensorFreeLeft_internalHomUncurry (X : PointedSymmetricSequence.{u})
    {A F : SymmetricSpectrum.{u}} (f : A ⟶ internalHom (freeObj X) F) :
    (MonoidalBalancedTensor.freeLeftIso sphereSequence.{u} X A).inv.hom ≫ (internalHomUncurry f).hom =
      X ◁ (f.hom ≫ (internalHomFreeUnderlyingIso X F).hom) ≫
        (ihom.ev X).app F.X := by
  rw [MonoidalBalancedTensor.freeLeftIso_inv sphereSequence.{u}, Category.assoc,
    tensorProjection_internalHomUncurry, ← whisker_exchange_assoc]
  change X ◁ f.hom ≫
    (generator X ▷ (internalHom (freeObj X) F).X ≫
      internalHomEvaluation (freeObj X) F) = _
  rw [← internalHomFreeUnderlyingIso_evaluation X F, ← whiskerLeft_comp_assoc]

/-- F_0との全体の逆比較の基礎射を、通常の内部Homの逆比較へ分解する。 -/
lemma internalHomCotensorIso_inv_hom (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorIso X E).inv.hom =
      (homBySequenceCotensorIso X E).inv ≫ (internalHomFreeAtIso 0 X E).inv.hom := by
  rfl

/-- cotensorの逆比較を自由原変数の比較へ戻すと、移送の逆射になる。 -/
lemma internalHomCotensorIso_inv_freeHom (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (internalHomCotensorIso X E).inv.hom ≫
        (internalHomFreeUnderlyingIso ((SymmetricSequence.freeAt 0).obj X) E).hom =
      (homBySequenceCotensorIso X E).inv := by
  rw [internalHomCotensorIso_inv_hom]
  simp only [internalHomFreeAtIso, internalHomFreeIso_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.SymmetricSpectrum
