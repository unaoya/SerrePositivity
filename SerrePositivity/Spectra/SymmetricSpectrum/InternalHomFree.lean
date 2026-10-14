module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFree
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFunctor

/-! # 自由スペクトルを原変数とする内部Hom

自由原変数からの内部Homを、生成対称列からの通常の内部Homへ比較する。
通常の内部Homには比較によって球面作用を移送する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由原変数の内部Homの基礎対称列と通常の内部Homの比較。 -/
abbrev internalHomFreeUnderlyingIso (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (internalHom (freeObj X) E).X ≅ (ihom X).obj E.X :=
  MonoidalModuleInternalHom.freeHomIso (C := PointedSymmetricSequence.{u}) sphereSequence.{u} X E

/-- 自由原変数の比較は生成元への制限後の転置。 -/
lemma internalHomFreeUnderlyingIso_hom (X : PointedSymmetricSequence.{u})
    (E : SymmetricSpectrum.{u}) : (internalHomFreeUnderlyingIso X E).hom =
      CategoryTheory.MonoidalClosed.curry
        (generator X ▷ (internalHom (freeObj X) E).X ≫ internalHomEvaluation (freeObj X) E) :=
  MonoidalModuleInternalHom.freeHomIso_hom
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} X E

/-- 比較と通常の内部Homの評価の合成は生成元上の評価。 -/
@[reassoc]
lemma internalHomFreeUnderlyingIso_evaluation (X : PointedSymmetricSequence.{u})
    (E : SymmetricSpectrum.{u}) :
    X ◁ (internalHomFreeUnderlyingIso X E).hom ≫ (ihom.ev X).app E.X =
      generator X ▷ (internalHom (freeObj X) E).X ≫ internalHomEvaluation (freeObj X) E :=
  by
    rw [internalHomFreeUnderlyingIso_hom]
    exact CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app
      (C := PointedSymmetricSequence.{u}) X E.X _

/-- 生成対称列からの通常の内部Homに球面作用を移送したスペクトル。 -/
abbrev homBySequence (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} :=
  MonoidalModuleInternalHom.freeHomObj (C := PointedSymmetricSequence.{u}) sphereSequence.{u} X E

/-- 移送した作用を持つスペクトルの基礎対称列。 -/
lemma homBySequence_underlying (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (homBySequence X E).X = (ihom X).obj E.X := rfl

/-- 自由原変数との比較はスペクトルとしての同型。 -/
abbrev internalHomFreeIso (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    internalHom (freeObj X) E ≅ homBySequence X E :=
  MonoidalModuleInternalHom.freeHomModuleIso
    (C := PointedSymmetricSequence.{u}) sphereSequence.{u} X E

/-- スペクトルの比較の順射は基礎対称列の比較。 -/
lemma internalHomFreeIso_hom (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (internalHomFreeIso X E).hom.hom = (internalHomFreeUnderlyingIso X E).hom := rfl

/-- スペクトルの比較の逆射は基礎対称列の逆比較。 -/
lemma internalHomFreeIso_inv (X : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (internalHomFreeIso X E).inv.hom = (internalHomFreeUnderlyingIso X E).inv := rfl

/-- 第n段からの自由スペクトルを原変数に置く内部Homの比較。 -/
def internalHomFreeAtIso (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    internalHom ((freeAt n).obj X) E ≅ homBySequence ((SymmetricSequence.freeAt n).obj X) E :=
  internalHomFreeIso ((SymmetricSequence.freeAt n).obj X) E

end SerrePositivity.SymmetricSpectrum
