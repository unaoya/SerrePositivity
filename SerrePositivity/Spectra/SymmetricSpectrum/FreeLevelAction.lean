module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionAction
public import SerrePositivity.Spectra.SymmetricSpectrum.FreeLevelInduction
public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons

/-! # 自由対称スペクトルの各段の作用付き誘導表示

誘導図式の余極限上の対称群作用と、自由スペクトルの各段の作用を比較する。
入力の射を同変射として扱い、比較同型の自然性を記述する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (levelMap)

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 自由スペクトルの誘導表示上の、出力の対称群作用。 -/
def freeAtLevelInductionAction (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    Action PointedSimplicialSet.{u} (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freeInductionAction sphereSequence.{u} n X m

/-- 固定した出力次数の、作用付き誘導表示の関手。 -/
def freeAtLevelInductionActionFunctor (n m : ℕ) :
    PointedSimplicialSet.{u} ⥤ Action PointedSimplicialSet.{u} (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freeInductionActionFunctor sphereSequence.{u} n m

/-- 自由スペクトルの各段と誘導表示との、対称群作用を備えた同型。 -/
def freeAtLevelActionIsoInduction (n : ℕ) (X : PointedSimplicialSet.{u}) (m : ℕ) :
    SymmetricSequence.levelAction ((freeAt n).obj X).X m ≅
      freeAtLevelInductionAction n X m :=
  SymmetricSequence.freeConvolutionLevelActionIsoInduction sphereSequence.{u} n X m

/-- 出力の全単射に関する誘導表示の自然性。 -/
@[reassoc] lemma freeAtLevelIsoInduction_output (n : ℕ) (X : PointedSimplicialSet.{u})
    {m m' : ℕ} (k : FiniteBijection.of m ⟶ FiniteBijection.of m') :
    ((freeAt n).obj X).X.map k ≫ (freeAtLevelIsoInduction n X m').hom =
      (freeAtLevelIsoInduction n X m).hom ≫
        SymmetricSequence.freeInductionOutputMap sphereSequence.{u} n X k :=
  SymmetricSequence.freeConvolutionLevelIsoInduction_output sphereSequence.{u} n X k

/-- 自由スペクトルの入力の射は、自由convolutionの入力の射と一致する。 -/
lemma freeAt_map_underlying (n : ℕ) {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    ((freeAt n).map f).hom = SymmetricSequence.freeConvolutionInputMap sphereSequence.{u} n f := by
  change sphereSequence.{u} ◁ (SymmetricSequence.freeAt n).map f = _
  apply Functor.hom_ext_of_isLeftKanExtension _
    (SymmetricSequence.convolutionUnit sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X))
  apply NatTrans.ext
  funext d
  change (SymmetricSequence.convolutionUnit sphereSequence.{u}
      ((SymmetricSequence.freeAt n).obj X)).app d ≫
        (sphereSequence.{u} ◁ (SymmetricSequence.freeAt n).map f).app
          (FiniteBijection.sumObj d.1 d.2) = _
  rw [SymmetricSequence.convolutionUnit_whiskerLeft]
  let η : externalProduct sphereSequence.{u} ((SymmetricSequence.freeAt n).obj X) ⟶
      externalProduct sphereSequence.{u} ((SymmetricSequence.freeAt n).obj Y) :=
    (externalProductBifunctor FiniteBijection FiniteBijection PointedSimplicialSet.{u}).map
      (𝟙 (SymmetricSequence.toFunctorCategory.obj sphereSequence.{u}),
        SymmetricSequence.toFunctorCategory.map ((SymmetricSequence.freeAt n).map f))
  have hn := congr_app (FiniteBijection.sumFunctor.lanUnit.naturality η) d
  change η.app d ≫ (SymmetricSequence.convolutionUnit sphereSequence.{u}
      ((SymmetricSequence.freeAt n).obj Y)).app d =
    (SymmetricSequence.convolutionUnit sphereSequence.{u}
      ((SymmetricSequence.freeAt n).obj X)).app d ≫
      (SymmetricSequence.freeConvolutionInputMap sphereSequence.{u} n f).app
        (FiniteBijection.sumObj d.1 d.2) at hn
  simpa only [η, externalProductBifunctor_map_app, NatTrans.id_app,
    SymmetricSequence.toFunctorCategory, id_whiskerRight, Category.id_comp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    SymmetricSequence.tensorObj_eq_convolution, FiniteBijection.sumFunctor, Prod.mk.eta] using hn

/-- 入力の射に関する誘導表示の自然性。 -/
@[reassoc] lemma freeAtLevelIsoInduction_input (n : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (m : ℕ) :
    levelMap ((freeAt n).map f) m ≫ (freeAtLevelIsoInduction n Y m).hom =
      (freeAtLevelIsoInduction n X m).hom ≫
        SymmetricSequence.freeInductionInputMap sphereSequence.{u} n f m := by
  change ((freeAt n).map f).hom.app (FiniteBijection.of m) ≫ _ = _
  rw [freeAt_map_underlying]
  exact SymmetricSequence.freeConvolutionLevelIsoInduction_input sphereSequence.{u} n f m

/-- 自由スペクトルの入力の射は生成元のXの因子に作用する。 -/
@[reassoc] lemma freeAtLevelGenerator_input (n : ℕ) {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (m : ℕ) (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    freeAtLevelGenerator n X m a h ≫ levelMap ((freeAt n).map f) m =
      sphereSequence.{u}.obj a ◁ f ≫ freeAtLevelGenerator n Y m a h := by
  change SymmetricSequence.freeConvolutionGenerator sphereSequence.{u} n X m a h ≫
    ((freeAt n).map f).hom.app (FiniteBijection.of m) = _
  rw [freeAt_map_underlying]
  exact SymmetricSequence.freeConvolutionGenerator_input sphereSequence.{u} n f m a h

/-- 自由スペクトルの作用付き各段と、誘導表示との自然同型。 -/
def freeAtLevelActionNatIsoInduction (n m : ℕ) :
    freeAt.{u} n ⋙ forget ⋙ SymmetricSequence.levelActionFunctor m ≅
      freeAtLevelInductionActionFunctor n m :=
  NatIso.ofComponents (fun X => freeAtLevelActionIsoInduction n X m) (by
    intro X Y f
    apply Action.hom_ext
    exact freeAtLevelIsoInduction_input n f m)

end SerrePositivity.SymmetricSpectrum
