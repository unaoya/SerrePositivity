module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassCommonBase
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientComposition
public import SerrePositivity.KST.LocalizingInvariants.DGBimoduleCokernel

/-!
概要：元の Postnikov class を係数商へ送ると、共通底上で実乗法的零経路を持つ。
方針：元の源の class の係数因子分解を保ち、相対経路を係数 cokernel へ後合成する。
規約：経路の向きは零切断から標的 class。使われ方：像への実導来 lift の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovClassCommonBaseSource_eq : postnikovClassCommonBaseSource R f n hn =
    cellAugmentation R (cellResolution R (postnikov R B n)) ≫ postnikovCellClass R B n hn ≫
      SquareZero.coefficientMap (postnikov R B n) (postnikovShiftedLayerMap R B n hn 1 f) := by
  apply SquareZero.baseChange_hom_ext (postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1)
  · rw [postnikovClassCommonBaseSource, SquareZero.baseChangeLift_projection,
      Category.assoc, Category.assoc, SquareZero.coefficientMap_projection]
    exact (congrArg (fun z => cellAugmentation R (cellResolution R (postnikov R B n)) ≫ z)
      (postnikovCellClass_projection R B n hn)).symm
  · rw [postnikovClassCommonBaseSource, SquareZero.baseChangeLift_map,
      Category.assoc, Category.assoc, SquareZero.coefficientMap_baseChangeMap]
    rfl

def postnikovClassCokernelWitness : Path.Witness R
    (classCommonBase R (B := B) n ≫ SquareZero.zeroSection (postnikov R B n)
      (DGBimoduleCokernel.obj (postnikovShiftedLayerMap R B n hn 1 f)))
    (postnikovClassCommonBaseTarget R f n hn ≫ SquareZero.coefficientMap (postnikov R B n)
      (DGBimoduleCokernel.projection (postnikovShiftedLayerMap R B n hn 1 f))) where
  hom := ((postnikovClassCommonBaseWitness R f n hn).postcomp
    (SquareZero.coefficientMap (postnikov R B n)
      (DGBimoduleCokernel.projection (postnikovShiftedLayerMap R B n hn 1 f)))).hom
  source_eq := by
    rw [((postnikovClassCommonBaseWitness R f n hn).postcomp
      (SquareZero.coefficientMap (postnikov R B n)
        (DGBimoduleCokernel.projection (postnikovShiftedLayerMap R B n hn 1 f)))).source_eq,
      postnikovClassCommonBaseSource_eq, Category.assoc, Category.assoc,
      SquareZero.coefficientMap_comp_zero _ _ (DGBimoduleCokernel.condition _),
      ← Category.assoc (postnikovCellClass R B n hn), postnikovCellClass_projection]
    rfl
  target_eq := ((postnikovClassCommonBaseWitness R f n hn).postcomp
    (SquareZero.coefficientMap (postnikov R B n)
      (DGBimoduleCokernel.projection (postnikovShiftedLayerMap R B n hn 1 f)))).target_eq

lemma postnikovClassCokernelWitness_relative : (postnikovClassCokernelWitness R f n hn).hom ≫
    Path.map R (SquareZero.projection (postnikov R B n)
      (DGBimoduleCokernel.obj (postnikovShiftedLayerMap R B n hn 1 f))) =
        classCommonBase R (B := B) n ≫ Path.diagonal R (postnikov R B n) := by
  change ((postnikovClassCommonBaseWitness R f n hn).hom ≫ Path.map R _) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, SquareZero.coefficientMap_projection,
    postnikovClassCommonBaseWitness_relative]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
