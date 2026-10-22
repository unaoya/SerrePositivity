module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroImageZeroStartDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassCokernelPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImage

/-!
概要：元の Postnikov class を、実係数像への実 class と derivation へ持ち上げる。
方針：構成済みの共通底上の乗法的 cokernel 零経路を、零切断第一脚の cell lift に渡す。
規約：三重 cell 源と元の包含・底への実経路を保持。使われ方：LT の像制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

abbrev postnikovImageClassSource :=
  cellResolution R (cellResolution R (cellResolution R (postnikov R B n)))

def postnikovImageClass : postnikovImageClassSource R (B := B) n ⟶
    SquareZero.algebra (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1) :=
  SquareZeroImageFiber.ZeroStart.derivedLift (postnikovShiftedLayerMap R B n hn 1 f)
    (postnikovClassCommonBaseTarget R f n hn) (classCommonBase R (B := B) n)
    (postnikovClassCokernelWitness R f n hn)

def postnikovImageBase : postnikovImageClassSource R (B := B) n ⟶ postnikov R B n :=
  postnikovImageClass R f n hn ≫
    SquareZero.projection (postnikov R B n) (postnikovShiftedLayerImage R f n hn 1)

def postnikovImageDerivation : SquareZero.Derivation (postnikovImageClassSource R (B := B) n)
    (bimoduleRestrict (postnikovImageBase R f n hn) (postnikovShiftedLayerImage R f n hn 1)) :=
  SquareZeroImageFiber.ZeroStart.derivedDerivation (postnikovShiftedLayerMap R B n hn 1 f)
    (postnikovClassCommonBaseTarget R f n hn) (classCommonBase R (B := B) n)
    (postnikovClassCokernelWitness R f n hn)

lemma postnikovImageDerivation_section : (postnikovImageDerivation R f n hn).section ≫
    SquareZero.mapOver (postnikovImageBase R f n hn) _ _
      (𝟙 (bimoduleRestrict (postnikovImageBase R f n hn) (postnikovShiftedLayerImage R f n hn 1))) =
        postnikovImageClass R f n hn :=
  SquareZeroImageFiber.ZeroStart.derivedDerivation_section _ _ _ _

def postnikovImageClassWitness : Path.Witness R (postnikovImageClass R f n hn ≫
    SquareZero.coefficientMap (postnikov R B n) (postnikovShiftedLayerImageInclusion R f n hn 1))
    (cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n))) ≫
      postnikovClassCommonBaseTarget R f n hn) :=
  SquareZeroImageFiber.ZeroStart.derivedLiftInclusionWitness _ _ _ _

def postnikovImageBaseWitness : Path.Witness R (postnikovImageBase R f n hn)
    (cellAugmentation R (cellResolution R (cellResolution R (postnikov R B n))) ≫
      classCommonBase R (B := B) n) :=
  SquareZeroImageFiber.ZeroStart.derivedBaseWitness _ _ _ _

lemma postnikovImageBase_quasiIso : QuasiIso (postnikovImageBase R f n hn).hom := by
  apply SquareZeroImageFiber.ZeroStart.derivedBase_quasiIso
  change QuasiIso ((cellAugmentation R (cellResolution R (postnikov R B n))).hom ≫
    (cellAugmentation R (postnikov R B n)).hom)
  exact quasiIso_comp _ _ (hφ := cellAugmentation_quasiIso R _)
    (hφ' := cellAugmentation_quasiIso R _)

lemma postnikovImageTargetBase_quasiIso (hf : QuasiIso (postnikovMap R f n).hom) :
    QuasiIso (postnikovImageBase R f n hn ≫ postnikovMap R f n).hom :=
  quasiIso_comp _ _ (hφ := postnikovImageBase_quasiIso R f n hn) (hφ' := hf)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
