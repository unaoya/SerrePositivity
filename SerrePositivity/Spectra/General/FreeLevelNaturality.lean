module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInductionAction
public import SerrePositivity.Spectra.General.FreeLevelInduction
public import SerrePositivity.Spectra.SymmetricSequence.DayUnitComparisons

/-! # 自由対称スペクトルの各段の作用付き誘導表示

誘導図式の余極限上の対称群作用と、自由スペクトルの各段の作用を比較する。
入力の射を同変射として扱い、比較同型の自然性を記述する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.GeneralSymmetricSpectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] {K : C}

/-- 固定した出力次数の、作用付き誘導表示の関手。 -/
def freeAtLevelInductionActionFunctor (n m : ℕ) :
    C ⥤ Action C (Equiv.Perm (Fin m)) :=
  SymmetricSequence.freeInductionActionFunctor (SymmetricSequence.tensorPowerSequence K) n m

/-- 自由スペクトルの入力の射は、自由convolutionの入力の射と一致する。 -/
lemma freeAt_map_underlying (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    ((freeAt (K := K) n).map f).hom = SymmetricSequence.freeConvolutionInputMap
    (SymmetricSequence.tensorPowerSequence K) n f := by
  change (SymmetricSequence.tensorPowerSequence K) ◁ (SymmetricSequence.freeAt n).map f = _
  apply Functor.hom_ext_of_isLeftKanExtension _
    (SymmetricSequence.convolutionUnit
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt n).obj X))
  apply NatTrans.ext
  funext d
  change (SymmetricSequence.convolutionUnit (SymmetricSequence.tensorPowerSequence K)
      ((SymmetricSequence.freeAt n).obj X)).app d ≫
        ((SymmetricSequence.tensorPowerSequence K) ◁ (SymmetricSequence.freeAt n).map f).app
          (FiniteBijection.sumObj d.1 d.2) = _
  rw [SymmetricSequence.convolutionUnit_whiskerLeft]
  let η : externalProduct
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt n).obj X) ⟶
      externalProduct
    (SymmetricSequence.tensorPowerSequence K) ((SymmetricSequence.freeAt n).obj Y) :=
    (externalProductBifunctor FiniteBijection FiniteBijection C).map
      (𝟙 (SymmetricSequence.toFunctorCategory.obj (SymmetricSequence.tensorPowerSequence K)),
        SymmetricSequence.toFunctorCategory.map ((SymmetricSequence.freeAt n).map f))
  have hn := congr_app (FiniteBijection.sumFunctor.lanUnit.naturality η) d
  change η.app d ≫ (SymmetricSequence.convolutionUnit (SymmetricSequence.tensorPowerSequence K)
      ((SymmetricSequence.freeAt n).obj Y)).app d =
    (SymmetricSequence.convolutionUnit (SymmetricSequence.tensorPowerSequence K)
      ((SymmetricSequence.freeAt n).obj X)).app d ≫
      (SymmetricSequence.freeConvolutionInputMap (SymmetricSequence.tensorPowerSequence K) n f).app
        (FiniteBijection.sumObj d.1 d.2) at hn
  simpa only [η, externalProductBifunctor_map_app, NatTrans.id_app,
    SymmetricSequence.toFunctorCategory, id_whiskerRight, Category.id_comp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    SymmetricSequence.tensorObj_eq_convolution, FiniteBijection.sumFunctor, Prod.mk.eta] using hn

/-- 入力の射に関する誘導表示の自然性。 -/
@[reassoc] lemma freeAtLevelIsoInduction_input (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (m : ℕ) :
    levelMap ((freeAt (K := K) n).map f) m ≫ (freeAtLevelIsoInduction (K := K) n Y m).hom =
      (freeAtLevelIsoInduction (K := K) n X m).hom ≫
        SymmetricSequence.freeInductionInputMap
    (SymmetricSequence.tensorPowerSequence K) n f m := by
  change ((freeAt (K := K) n).map f).hom.app (FiniteBijection.of m) ≫ _ = _
  rw [freeAt_map_underlying]
  exact SymmetricSequence.freeConvolutionLevelIsoInduction_input
    (SymmetricSequence.tensorPowerSequence K) n f m

/-- 自由スペクトルの作用付き各段と、誘導表示との自然同型。 -/
def freeAtLevelActionNatIsoInduction (n m : ℕ) :
    freeAt (K := K) n ⋙ forget K ⋙ SymmetricSequence.levelActionFunctor m ≅
      freeAtLevelInductionActionFunctor (K := K) n m :=
  NatIso.ofComponents (fun X => SymmetricSequence.freeConvolutionLevelActionIsoInduction
    (SymmetricSequence.tensorPowerSequence K) n X m) (by
    intro X Y f
    apply Action.hom_ext
    exact freeAtLevelIsoInduction_input n f m)

end SerrePositivity.GeneralSymmetricSpectrum
