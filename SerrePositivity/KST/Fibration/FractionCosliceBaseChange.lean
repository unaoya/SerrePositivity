module
public import SerrePositivity.KST.Fibration.FractionFamilyCoslice
public import SerrePositivity.InfinityCategories.F1.BaseChange

/-! # 同じ全分数評価を底と任意の底図式を厳密に保った coslice 比較へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x : X _⦋0⦌)

/-- 任意の底図式上の分数族を、同じ商像の coslice 族へ送る実関手。 -/
def fractionCosliceBaseChange {A : SSet.{u}} (k : A ⟶ X) :
    pullback (markedSpanFamilyProjection X W x) k ⟶
      pullback (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (k ≫ F) :=
  pullback.lift (pullback.fst _ k ≫ fractionFamilyCosliceEvaluation F W hF x)
    (pullback.snd _ k) (by
      rw [Category.assoc, fractionFamilyCosliceEvaluation_projection,
        ← Category.assoc, pullback.condition, Category.assoc])

/-- coslice への元の評価を、第一射影が厳密に回収する。 -/
theorem fractionCosliceBaseChange_fst {A : SSet.{u}} (k : A ⟶ X) :
    fractionCosliceBaseChange F W hF x k ≫ pullback.fst _ (k ≫ F) =
      pullback.fst (markedSpanFamilyProjection X W x) k ≫
        fractionFamilyCosliceEvaluation F W hF x := pullback.lift_fst _ _ _

/-- 元の底図式の射影は、同じ分数比較によって全単体で厳密に保持される。 -/
theorem fractionCosliceBaseChange_snd {A : SSet.{u}} (k : A ⟶ X) :
    fractionCosliceBaseChange F W hF x k ≫ pullback.snd _ (k ≫ F) =
      pullback.snd (markedSpanFamilyProjection X W x) k := pullback.lift_snd _ _ _

end SerrePositivity.KST.Fibration
