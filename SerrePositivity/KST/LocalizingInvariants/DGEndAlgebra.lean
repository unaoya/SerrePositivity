module

public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：実 dg 圏の対象の自己準同型を、通常順の積を持つ実非可換 dg 代数にする。
方針：元の enriched 単位・合成を使い、unitor の逆を消してモノイド則へ戻す。
規約：反対代数にはしない。使われ方：一対象 cell 分解の実 dg 代数化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

def dgEndAlgebra (x : D) : Mon (Complex R) where
  X := x ⟶[Complex R] x
  mon := {
    one := eId (Complex R) x
    mul := eComp (Complex R) x x x
    one_mul := by
      apply (cancel_epi (λ_ (x ⟶[Complex R] x)).inv).1
      simpa only [Iso.inv_hom_id] using e_id_comp (Complex R) x x
    mul_one := by
      apply (cancel_epi (ρ_ (x ⟶[Complex R] x)).inv).1
      simpa only [Iso.inv_hom_id] using e_comp_id (Complex R) x x
    mul_assoc := (e_assoc' (Complex R) x x x x).symm }

def dgEndAlgebraMap {E : Type w} [DGCategory R E] (F : DGFunctor R D E) (x : D) :
    dgEndAlgebra R D x ⟶ dgEndAlgebra R E (F.obj x) :=
  Mon.Hom.mk' (F.map x x) (F.map_id x) (F.map_comp x x x)

end SerrePositivity.KST.LocalizingInvariants
