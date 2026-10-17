module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleMap
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions

/-! # 中間制限比較の値を固定した成分関数で表示する -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 中間制限比較の構成を展開せずに使う、型を固定した次数別成分関数。 -/
@[irreducible]
def middleRestrictionValueComponent (d : B) (e : E) (n : ℤ) :
    ((compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value d e).X n →
      ((compose A B C E P Q).value d e).X n :=
  fun x => (middleRestrictionComparisonValue A B C D E F P Q d e).f n x

lemma middleRestrictionValueComponent_eq (d : B) (e : E) (n : ℤ) (x) :
    middleRestrictionValueComponent A B C D E F P Q d e n x =
      (middleRestrictionComparisonValue A B C D E F P Q d e).f n x := by
  unfold middleRestrictionValueComponent
  rfl

/-- 固定成分による再表示は、元の中間制限比較と同じchain mapである。 -/
def middleRestrictionValueHom (d : B) (e : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value d e ⟶
      (compose A B C E P Q).value d e :=
  chainMapOfComponentFunctions (middleRestrictionComparisonValue A B C D E F P Q d e)
    (middleRestrictionValueComponent A B C D E F P Q d e)
    (middleRestrictionValueComponent_eq A B C D E F P Q d e)

@[simp]
lemma middleRestrictionValueHom_apply (d : B) (e : E) (n : ℤ) (x) :
    (middleRestrictionValueHom A B C D E F P Q d e).f n x =
      middleRestrictionValueComponent A B C D E F P Q d e n x := rfl

lemma middleRestrictionValueHom_eq (d : B) (e : E) :
    middleRestrictionValueHom A B C D E F P Q d e =
      (middleRestrictionComparisonValue A B C D E F P Q d e) :=
  chainMapOfComponentFunctions_eq _ _ _

lemma middleRestrictionValueComponent_element (b : B) (d : D) (e : E)
    {r s n : ℤ} (hn : r + s = n) (q : (Q.value (F.obj d) e).X r)
    (p : (P.value b (F.obj d)).X s) :
    middleRestrictionValueComponent A B C D E F P Q b e n
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) (F.obj d) q p hn :=
  (middleRestrictionValueComponent_eq A B C D E F P Q b e n _).trans
    (middleRestrictionComparisonValue_element A B C D E F P Q b e d q p hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
