module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestriction
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule

/-! # 中間dg圏の制限とbimodule合成の値での比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

/-- 制限した二因子のbalanced族を元のtensorの包含で指定する。 -/
def middleRestrictionFamily (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    BalancedTensor.BalancedFamily A D
      ((Bimodule.rightRestriction A C D E F Q).rightAt e)
      ((Bimodule.leftRestriction A B C D F P).leftAt b)
      (BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)) := by
  refine ⟨fun d => BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d), ?_⟩
  intro x y
  have h := (BalancedTensor.restrictFamily A D C F (Q.rightAt e) (P.leftAt b)
    ⟨fun c => BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c,
      BalancedTensor.condition A C (Q.rightAt e) (P.leftAt b)⟩).property x y
  have hl : BalancedTensor.leftAction A D
      ((Bimodule.leftRestriction A B C D F P).leftAt b) x y =
      BalancedTensor.leftAction A D (F.comp (P.leftAt b)) x y := by
    change uncurryRight ((F.map x y ≫ P.map (F.obj x) (F.obj y)) ≫
      moduleHomπ A B _ _ b) = uncurryRight
        (F.map x y ≫ (P.map (F.obj x) (F.obj y) ≫ moduleHomπ A B _ _ b))
    rw [Category.assoc]
  rw [hl]
  exact h

lemma middleRestrictionFamily_val (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) :
    (middleRestrictionFamily A B C D E F P Q b e).val d =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d) := rfl

/-- 二つの制限の合成から元の合成への、各値での実際のchain map。 -/
def middleRestrictionComparisonValue (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).value b e ⟶
        (compose A B C E P Q).value b e :=
  BalancedTensor.desc A D _ _ (middleRestrictionFamily A B C D E F P Q b e)

@[reassoc (attr := simp)]
lemma ι_middleRestrictionComparisonValue (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) :
    BalancedTensor.ι A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
        ((Bimodule.leftRestriction A B C D F P).leftAt b) d ≫
          middleRestrictionComparisonValue A B C D E F P Q b e =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) (F.obj d) := by
  exact (BalancedTensor.ι_desc A D _ _
    (middleRestrictionFamily A B C D E F P Q b e) d).trans
      (middleRestrictionFamily_val A B C D E F P Q b e d)

lemma middleRestrictionComparisonValue_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (b : B) (e : E) (d : D) {r s n : ℤ}
    (q : (Q.value (F.obj d) e).X r) (p : (P.value b (F.obj d)).X s) (hn : r + s = n) :
    (middleRestrictionComparisonValue A B C D E F P Q b e).f n
        (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
          ((Bimodule.leftRestriction A B C D F P).leftAt b) d q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) (F.obj d) q p hn :=
  congrArg (fun k => k.f n
    (ιTensorObj (Q.value (F.obj d) e) (P.value b (F.obj d)) r s n hn (q ⊗ₜ[A] p)))
      (ι_middleRestrictionComparisonValue A B C D E F P Q b e d)

end SerrePositivity.DifferentialGraded.BimoduleTensor
