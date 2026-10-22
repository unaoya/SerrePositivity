module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModels
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：二切断候補で使った同じ class 経路を、底を固定した相対経路に束ねる。
方針：元の classWitness の底への定数射影を保持し、新しい逆・合成の厳密な相殺を適用する。
規約：元の共通源を細分しない。使われ方：候補 roof の実逆三角形の経路補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def classRelativeWitness : SquareZero.RelativeWitness (d.classProjection R) (d.numeratorLayer R)
    (d.imageClass R) (d.targetClass R) where
  hom := (d.comparisonPath R).hom
  source_eq := (d.comparisonPath R).source_eq
  target_eq := (d.comparisonPath R).target_eq.trans (Category.id_comp _)
  projection_eq := d.classWitness_projection R

lemma classRelativeWitness_hom : (d.classRelativeWitness R).hom = (d.comparisonPath R).hom := rfl

lemma classRelativeWitness_comp_reverse :
    ((d.classRelativeWitness R).comp (d.classRelativeWitness R).reverse).hom =
      d.imageClass R ≫ Path.diagonal R (SquareZero.algebra (d.classBase R) (d.numeratorLayer R)) :=
  SquareZero.RelativeWitness.comp_reverse_hom _

lemma classRelativeWitness_reverse_comp :
    ((d.classRelativeWitness R).reverse.comp (d.classRelativeWitness R)).hom =
      d.targetClass R ≫ Path.diagonal R (SquareZero.algebra (d.classBase R) (d.numeratorLayer R)) :=
  SquareZero.RelativeWitness.reverse_comp_hom _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
