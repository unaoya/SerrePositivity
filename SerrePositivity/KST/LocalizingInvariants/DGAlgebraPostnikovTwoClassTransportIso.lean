module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRelativeModels
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof

/-!
概要：元の二切断 class 経路は、係数像模型と標準模型の実相対代数同型を与える。
方針：構成済みの同じ相対経路を transportIso に渡し、元の絶対模型の準同型 span へ戻す。
規約：追加の class 経路を入力しない。使われ方：候補 roof の実三角形の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def classRelativeTransportIso : d.imageRelativeModel R ≅ d.targetRelativeModel R :=
  SquareZeroExtension.transportIso (d.numeratorLayer R) (d.classRelativeWitness R)

lemma classRelativeTransportIso_left : (d.classRelativeTransportIso R).hom ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.imageClass R) :=
  SquareZeroExtension.transport_left _ _

lemma classRelativeTransportIso_right : (d.classRelativeTransportIso R).hom ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.imageClass R) :=
  SquareZeroExtension.transport_right _ _

def classRelativePathRoof : SurjectiveRoof R (d.imageModel R) (d.targetModel R) :=
  (SurjectiveRoof.ofQuasiIsoInverse R (d.imageRelativeComparison R)
    (d.imageRelativeComparison_quasiIso R)).postcompose R
      ((d.classRelativeTransportIso R).hom ≫ d.targetRelativeComparison R)

lemma classRelativePathRoof_numerator_quasiIso :
    QuasiIso (d.classRelativePathRoof R).numerator.hom := by
  have hi : QuasiIso (d.classRelativeTransportIso R).hom.hom := by
    have : IsIso (d.classRelativeTransportIso R).hom.hom := by
      change IsIso ((Mon.forget (Complex R)).map (d.classRelativeTransportIso R).hom)
      infer_instance
    exact quasiIso_of_isIso _
  change QuasiIso ((MappingPath.projection R (d.imageRelativeComparison R) ≫
    (d.classRelativeTransportIso R).hom ≫ d.targetRelativeComparison R).hom)
  exact quasiIso_comp _ _ (hφ := MappingPath.projection_quasiIso R _)
    (hφ' := quasiIso_comp _ _ (hφ := hi) (hφ' := d.targetRelativeComparison_quasiIso R))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
