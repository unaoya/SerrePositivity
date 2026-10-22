module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerZeroRestrictionIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver

/-!
概要：元の Postnikov class 標的を、同じ係数を持つ零底の実平方零代数へ写す。
方針：底切断遷移の作用比較から恒等係数射を作り、shift と平方零の実射へ移す。
規約：係数と元の遷移を保持。使われ方：三つの class 比較経路の共通標的。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovLayerToZeroBase : postnikovLayerBaseBimodule R B n hn ⟶
    bimoduleRestrict (postnikovTransition R B n 0 hn) (postnikovLayerZeroBimodule R B n) where
  hom := 𝟙 (postnikovLayer R B n)
  left_act_hom := by
    change (postnikovLayerBaseBimodule R B n hn).actLeft ≫ 𝟙 _ =
      ((postnikov R B n).X ◁ 𝟙 (postnikovLayer R B n)) ≫
        ((postnikovTransition R B n 0 hn).hom ▷ postnikovLayer R B n) ≫
          (postnikovLayerZeroBimodule R B n).actLeft
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp]
    exact (postnikovLayerBase_zero_left_transition R B n hn).symm
  right_act_hom := by
    change (postnikovLayerBaseBimodule R B n hn).actRight ≫ 𝟙 _ =
      (𝟙 (postnikovLayer R B n) ▷ (postnikov R B n).X) ≫
        (postnikovLayer R B n ◁ (postnikovTransition R B n 0 hn).hom) ≫
          (postnikovLayerZeroBimodule R B n).actRight
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
    exact (postnikovLayerBase_zero_right_transition R B n hn).symm

lemma postnikovLayerToZeroBase_hom : (postnikovLayerToZeroBase R B n hn).hom =
    𝟙 (postnikovLayer R B n) := rfl

def postnikovShiftedLayerToZeroBase (s : ℤ) : postnikovShiftedLayerBimodule R B n hn s ⟶
    bimoduleRestrict (postnikovTransition R B n 0 hn)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s) :=
  DGBimoduleShift.mapOver _ _ s (postnikovLayerToZeroBase R B n hn)

lemma postnikovShiftedLayerToZeroBase_hom (s : ℤ) :
    (postnikovShiftedLayerToZeroBase R B n hn s).hom = 𝟙 ((postnikovLayer R B n)⟦s⟧) := by
  rw [postnikovShiftedLayerToZeroBase, DGBimoduleShift.mapOver_hom, postnikovLayerToZeroBase_hom]
  change (shiftFunctor (Complex R) s).map (𝟙 (postnikovLayer R B n)) = 𝟙 _
  exact (shiftFunctor (Complex R) s).map_id _

def postnikovZeroClassTarget (s : ℤ) : Mon (Complex R) :=
  SquareZero.algebra (postnikov R B 0) (DGBimoduleShift.obj (postnikovLayerZeroBimodule R B n) s)

def postnikovClassToZeroBase (s : ℤ) :
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn s) ⟶
      postnikovZeroClassTarget R B n s :=
  SquareZero.mapOver _ _ _ (postnikovShiftedLayerToZeroBase R B n hn s)

lemma postnikovClassToZeroBase_projection (s : ℤ) : postnikovClassToZeroBase R B n hn s ≫
    SquareZero.projection _ _ = SquareZero.projection _ _ ≫ postnikovTransition R B n 0 hn :=
  SquareZero.mapOver_projection _ _ _ _

lemma postnikovClassToZeroBase_hom (s : ℤ) : (postnikovClassToZeroBase R B n hn s).hom =
    biprod.map (postnikovTransition R B n 0 hn).hom (𝟙 ((postnikovLayer R B n)⟦s⟧)) := by
  change biprod.map (postnikovTransition R B n 0 hn).hom
    (postnikovShiftedLayerToZeroBase R B n hn s).hom = _
  rw [postnikovShiftedLayerToZeroBase_hom]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
