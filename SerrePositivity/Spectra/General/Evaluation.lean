module

public import SerrePositivity.Spectra.SymmetricSequence.Evaluation
public import SerrePositivity.Spectra.General.Free

/-! # 第n段を生成する自由対称スペクトル

対称列の評価の左随伴と自由Sym(K)加群を合成する。
Cの対象Xから第n段を生成するF_n Xは、スペクトルの第n段の評価の左随伴。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.GeneralSymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] {K : C}

/-- スペクトルの置換作用を忘れた第n段の評価。 -/
def evaluation (n : ℕ) : GeneralSymmetricSpectrum C K ⥤ C :=
  forget K ⋙ SymmetricSequence.evaluation n

/-- Cの対象から第n段を生成する自由スペクトル関手F_n。 -/
def freeAt (n : ℕ) : C ⥤ GeneralSymmetricSpectrum C K :=
  SymmetricSequence.freeAt n ⋙ freeFunctor K

/-- F_nと第n段の評価との随伴。 -/
def freeAtAdjunction (n : ℕ) : freeAt (K := K) n ⊣ evaluation (K := K) n :=
  (SymmetricSequence.freeAtAdjunction n).comp (freeForgetAdjunction K)

/-- 自由スペクトルの射は第n段への射と同値。 -/
def freeAtHomEquiv (n : ℕ) (X : C) (E : GeneralSymmetricSpectrum C K) :
    ((freeAt (K := K) n).obj X ⟶ E) ≃ (X ⟶ level E n) :=
  (freeAtAdjunction (K := K) n).homEquiv X E

/-- F_n Xの第n段への生成元の射。 -/
def freeAtGenerator (n : ℕ) (X : C) :
    X ⟶ level ((freeAt (K := K) n).obj X) n := (freeAtAdjunction (K := K) n).unit.app X

/-- 第n段で指定した射から自由スペクトルの射への延長。 -/
def freeAtLift (n : ℕ) {X : C} (E : GeneralSymmetricSpectrum C K)
    (f : X ⟶ level E n) : (freeAt (K := K) n).obj X ⟶ E := (freeAtHomEquiv (K := K) n X E).symm f

/-- 生成元は自由対称列の生成元と、自由Sym(K)加群の生成元との合成。 -/
lemma freeAtGenerator_eq (n : ℕ) (X : C) :
    freeAtGenerator (K := K) n X = SymmetricSequence.freeAtGenerator n X ≫
      (generator K ((SymmetricSequence.freeAt n).obj X)).app (FiniteBijection.of n) := by
  rw [freeAtGenerator, freeAtAdjunction, Adjunction.comp_unit_app,
    SymmetricSequence.freeAt_unit, MonoidalFreeModule.free_unit]
  rfl

/-- 第n段で指定した値を持つ自由スペクトルの射は一意。 -/
lemma freeAtLift_unique (n : ℕ) {X : C}
    (E : GeneralSymmetricSpectrum C K) (f : (freeAt (K := K) n).obj X ⟶ E) (g : X ⟶ level E n)
    (h : freeAtGenerator (K := K) n X ≫ levelMap f n = g) : f = freeAtLift (K := K) n E g := by
  apply (freeAtHomEquiv (K := K) n X E).injective
  erw [(freeAtAdjunction (K := K) n).homEquiv_unit X E f, h]
  exact ((freeAtHomEquiv (K := K) n X E).apply_symm_apply g).symm

/-- 延長は、自由対称列への延長と自由Sym(K)加群への延長を順に行う構成。 -/
lemma freeAtLift_eq (n : ℕ) {X : C}
    (E : GeneralSymmetricSpectrum C K) (f : X ⟶ level E n) :
    freeAtLift (K := K) n E f = lift K E (SymmetricSequence.freeAtLift n E.X f) := by
  symm
  apply freeAtLift_unique (K := K) n E _ f
  change freeAtGenerator (K := K) n X ≫
    (lift K E (SymmetricSequence.freeAtLift n E.X f)).hom.app (FiniteBijection.of n) = f
  rw [freeAtGenerator_eq (K := K)]
  erw [Category.assoc, ← NatTrans.comp_app, generator_lift]
  exact SymmetricSequence.freeAtGenerator_lift n E.X f

end SerrePositivity.GeneralSymmetricSpectrum
