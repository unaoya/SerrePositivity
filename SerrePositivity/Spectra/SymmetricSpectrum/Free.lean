module

public import SerrePositivity.CategoryTheory.Monoidal.FreeModule
public import SerrePositivity.Spectra.SymmetricSpectrum.Sphere

/-! # 自由対称スペクトルと忘却関手の随伴

一般のモノイダル圏の自由内部加群を球面モノイドへ特殊化する。
生成元によるHom同値、延長の一意性、随伴の単位・余単位を比較する。
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SymmetricSpectrum
open SerrePositivity.PointedSimplicialSet
/-- 対称列Fを生成元とする自由球面加群。 -/
def freeObj (F : PointedSymmetricSequence.{u}) : SymmetricSpectrum.{u} :=
  MonoidalFreeModule.freeObj sphereSequence.{u} F
/-- 対称列から自由対称スペクトルを作る関手。 -/
def freeFunctor : PointedSymmetricSequence.{u} ⥤ SymmetricSpectrum.{u} :=
  MonoidalFreeModule.freeFunctor sphereSequence.{u}
/-- 対称列から自由対称スペクトルへの生成元の射。 -/
def generator (F : PointedSymmetricSequence.{u}) : F ⟶ (freeObj F).X :=
  MonoidalFreeModule.generator sphereSequence.{u} F
/-- 生成元の対称列の射から、自由対称スペクトルの射への延長。 -/
def lift {F : PointedSymmetricSequence.{u}} (E : SymmetricSpectrum.{u}) (f : F ⟶ E.X) :
    freeObj F ⟶ E := MonoidalFreeModule.lift sphereSequence.{u} F E f
/-- 自由対称スペクトルの射と、生成元の対称列の射との同値。 -/
def freeHomEquiv (F : PointedSymmetricSequence.{u}) (E : SymmetricSpectrum.{u}) :
    (freeObj F ⟶ E) ≃ (F ⟶ E.X) := MonoidalFreeModule.freeHomEquiv sphereSequence.{u} F E
/-- 自由対称スペクトル関手と忘却関手の随伴。 -/
def freeForgetAdjunction : freeFunctor.{u} ⊣ forget.{u} :=
  MonoidalFreeModule.freeForgetAdjunction sphereSequence.{u}
/-- 自由対称スペクトルの underlying 対称列は球面とのconvolution。 -/
lemma free_underlying (F : PointedSymmetricSequence.{u}) :
    (freeObj F).X = sphereSequence.{u} ⊗ F := rfl
/-- 自由対称スペクトルの作用は球面の乗法から得る射。 -/
lemma free_action (F : PointedSymmetricSequence.{u}) :
    action (freeObj F) = (α_ sphereSequence.{u} sphereSequence.{u} F).inv ≫
      (sphereMultiplication.{u} ▷ F) := rfl
/-- 延長した射は生成元上で元の射に一致する。 -/
lemma generator_lift {F : PointedSymmetricSequence.{u}} (E : SymmetricSpectrum.{u}) (f : F ⟶ E.X) :
    generator F ≫ (lift E f).hom = f := MonoidalFreeModule.generator_lift sphereSequence.{u} F E f
/-- 自由対称スペクトルの射は生成元での値からの延長に等しい。 -/
lemma lift_generator {F : PointedSymmetricSequence.{u}} (E : SymmetricSpectrum.{u})
    (f : freeObj F ⟶ E) : lift E (generator F ≫ f.hom) = f :=
  MonoidalFreeModule.lift_generator sphereSequence.{u} F E f
/-- 生成元で指定した値を持つスペクトルの射は一意。 -/
lemma lift_unique {F : PointedSymmetricSequence.{u}} (E : SymmetricSpectrum.{u})
    (f : freeObj F ⟶ E) (g : F ⟶ E.X) (h : generator F ≫ f.hom = g) : f = lift E g := by
  apply (freeHomEquiv F E).injective
  exact h.trans (generator_lift E g).symm
/-- 自由・忘却の随伴の単位は生成元の射。 -/
lemma free_unit (F : PointedSymmetricSequence.{u}) :
    freeForgetAdjunction.{u}.unit.app F = generator F :=
  MonoidalFreeModule.free_unit sphereSequence.{u} F
/-- 自由・忘却の随伴の余単位の underlying 射は球面の作用。 -/
lemma free_counit (E : SymmetricSpectrum.{u}) :
    (freeForgetAdjunction.{u}.counit.app E).hom = action E :=
  MonoidalFreeModule.free_counit sphereSequence.{u} E
/-- 自由スペクトルの作用を忘れると球面との左convolutionになる。 -/
lemma free_forget_eq_tensorLeft :
    freeFunctor.{u} ⋙ forget.{u} = tensorLeft sphereSequence.{u} := rfl
end SerrePositivity.SymmetricSpectrum
