module

public import SerrePositivity.Spectra.SymmetricSequence.Evaluation
public import SerrePositivity.Spectra.SymmetricSpectrum.Free

/-! # 第n段を生成する自由対称スペクトル

対称列の評価の左随伴と自由球面加群を合成する。
基点付き単体的集合Xから第n段を生成するF_n Xは、スペクトルの第n段の評価の左随伴。
-/

@[expose] public section

universe u

noncomputable section

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory

/-- スペクトルの置換作用を忘れた第n段の評価。 -/
def evaluation (n : ℕ) : SymmetricSpectrum.{u} ⥤ PointedSimplicialSet.{u} :=
  forget ⋙ SymmetricSequence.evaluation n

/-- 基点付き単体的集合から第n段を生成する自由スペクトル関手F_n。 -/
def freeAt (n : ℕ) : PointedSimplicialSet.{u} ⥤ SymmetricSpectrum.{u} :=
  SymmetricSequence.freeAt n ⋙ freeFunctor

/-- F_nと第n段の評価との随伴。 -/
def freeAtAdjunction (n : ℕ) : freeAt.{u} n ⊣ evaluation n :=
  (SymmetricSequence.freeAtAdjunction n).comp freeForgetAdjunction

/-- 自由スペクトルの射は第n段への基点付き射と同値。 -/
def freeAtHomEquiv (n : ℕ) (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    ((freeAt n).obj X ⟶ E) ≃ (X ⟶ level E n) :=
  (freeAtAdjunction n).homEquiv X E

/-- F_n Xの第n段への生成元の射。 -/
def freeAtGenerator (n : ℕ) (X : PointedSimplicialSet.{u}) :
    X ⟶ level ((freeAt n).obj X) n := (freeAtAdjunction n).unit.app X

/-- 第n段で指定した射から自由スペクトルの射への延長。 -/
def freeAtLift (n : ℕ) {X : PointedSimplicialSet.{u}} (E : SymmetricSpectrum.{u})
    (f : X ⟶ level E n) : (freeAt n).obj X ⟶ E := (freeAtHomEquiv n X E).symm f

/-- 生成元は自由対称列の生成元と、自由球面加群の生成元との合成。 -/
lemma freeAtGenerator_eq (n : ℕ) (X : PointedSimplicialSet.{u}) :
    freeAtGenerator n X = SymmetricSequence.freeAtGenerator n X ≫
      (generator ((SymmetricSequence.freeAt n).obj X)).app (FiniteBijection.of n) := by
  rw [freeAtGenerator, freeAtAdjunction, Adjunction.comp_unit_app,
    SymmetricSequence.freeAt_unit, free_unit]
  rfl

/-- Hom同値はスペクトルの射を生成元へ制限する。 -/
lemma freeAtHomEquiv_apply (n : ℕ) (X : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (f : (freeAt n).obj X ⟶ E) :
    freeAtHomEquiv n X E f = freeAtGenerator n X ≫ levelMap f n :=
  (freeAtAdjunction n).homEquiv_unit X E f

/-- 延長は第n段の生成元上で元の射に一致する。 -/
lemma freeAtGenerator_lift (n : ℕ) {X : PointedSimplicialSet.{u}}
    (E : SymmetricSpectrum.{u}) (f : X ⟶ level E n) :
    freeAtGenerator n X ≫ levelMap (freeAtLift n E f) n = f := by
  rw [← freeAtHomEquiv_apply]
  exact (freeAtHomEquiv n X E).apply_symm_apply f

/-- 自由スペクトルの射は生成元での値からの延長に等しい。 -/
lemma freeAtLift_generator (n : ℕ) {X : PointedSimplicialSet.{u}}
    (E : SymmetricSpectrum.{u}) (f : (freeAt n).obj X ⟶ E) :
    freeAtLift n E (freeAtGenerator n X ≫ levelMap f n) = f := by
  rw [← freeAtHomEquiv_apply]
  exact (freeAtHomEquiv n X E).symm_apply_apply f

/-- 第n段で指定した値を持つ自由スペクトルの射は一意。 -/
lemma freeAtLift_unique (n : ℕ) {X : PointedSimplicialSet.{u}}
    (E : SymmetricSpectrum.{u}) (f : (freeAt n).obj X ⟶ E) (g : X ⟶ level E n)
    (h : freeAtGenerator n X ≫ levelMap f n = g) : f = freeAtLift n E g := by
  apply (freeAtHomEquiv n X E).injective
  rw [freeAtHomEquiv_apply, h]
  exact ((freeAtHomEquiv n X E).apply_symm_apply g).symm

/-- 延長は、自由対称列への延長と自由球面加群への延長を順に行う構成。 -/
lemma freeAtLift_eq (n : ℕ) {X : PointedSimplicialSet.{u}}
    (E : SymmetricSpectrum.{u}) (f : X ⟶ level E n) :
    freeAtLift n E f = lift E (SymmetricSequence.freeAtLift n E.X f) := by
  symm
  apply freeAtLift_unique n E _ f
  change freeAtGenerator n X ≫
    (lift E (SymmetricSequence.freeAtLift n E.X f)).hom.app (FiniteBijection.of n) = f
  rw [freeAtGenerator_eq]
  erw [Category.assoc, ← NatTrans.comp_app, generator_lift]
  exact SymmetricSequence.freeAtGenerator_lift n E.X f

/-- F_n Xのunderlying対称列は球面と自由対称列のconvolution。 -/
lemma freeAt_underlying (n : ℕ) (X : PointedSimplicialSet.{u}) :
    ((freeAt n).obj X).X =
      PointedSimplicialSet.sphereSequence.{u} ⊗ (SymmetricSequence.freeAt n).obj X := rfl

end SerrePositivity.SymmetricSpectrum
