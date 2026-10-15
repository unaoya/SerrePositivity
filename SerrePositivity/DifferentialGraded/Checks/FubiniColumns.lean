module
public import SerrePositivity.DifferentialGraded.Tensor.FubiniColumns
public import SerrePositivity.DifferentialGraded.Tensor.DegreeElementsExt
public import SerrePositivity.DifferentialGraded.Tensor.ParameterBalancedElements
public import Mathlib.Data.ZMod.Basic

/-! # 二重balanced族のE方向の降下と固定次数の外延性の検査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
open SerrePositivity.DifferentialGraded.BalancedTensor.Fubini
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A)
    (a : DoubleFamily A C E Q R N T) (c : C) :
    RightParamFamily A E R (Q.leftAt c) (N.obj c) T := columnFamily A C E a c

example (Q : Bimodule A C E) (R : RightModule A E) (N : LeftModule A C) (T : Complex A)
    (a : DoubleFamily A C E Q R N T) (c : C) (e : E)
    (t : (R.obj (op e)).X (-1)) (q : (Q.value c e).X 2) (v : (N.obj c).X (-1)) :
    (columnDesc A C E a c).f 0
      (ιTensorObj ((rightModule A C E Q R).obj (op c)) (N.obj c) 1 (-1) 0 (by decide)
        (element A E R (Q.leftAt c) e t q (by decide) ⊗ₜ[A] v)) =
    tripleElement A C E (n := 0) (fun c e => (a.row e).val c) c e t q v rfl (by decide) :=
  columnDesc_element A C E a c e (by decide) (by decide) t q v

example (Q : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (R : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2)) (a : DoubleFamily (ZMod 2) PUnit.{1} PUnit.{1} Q R N T)
    (c : PUnit.{1}) :
    (rightModule (ZMod 2) PUnit.{1} PUnit.{1} Q R).obj (op c) ⊗ N.obj c ⟶ T :=
  columnDesc (ZMod 2) PUnit.{1} PUnit.{1} a c

#print axioms DoubleFamily.balanceE_of_sums
#print axioms columnMaps
#print axioms columnCurry
#print axioms columnFamily
#print axioms columnDesc
#print axioms ι_columnDesc
#print axioms columnDesc_element
#print axioms degree_element_ext
#print axioms paramFamily_balanced_element
