module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionFamilyCoslice
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-! # 同じ全分数評価を底と任意の底図式を厳密に保った coslice 比較へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x : X _⦋0⦌)

/-- 任意の底図式上の分数族を、同じ商像の coslice 族へ送る実関手。 -/
def fractionCosliceBaseChange {A : SSet.{u}} (k : A ⟶ X) :
    pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) k ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (k ≫ F) :=
  pullback.lift (pullback.fst _ k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x)
    (pullback.snd _ k) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceEvaluation_projection,
        ← Category.assoc, pullback.condition, Category.assoc])

/-- coslice への元の評価を、第一射影が厳密に回収する。 -/
theorem fractionCosliceBaseChange_fst {A : SSet.{u}} (k : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange F W hF x k ≫ pullback.fst _ (k ≫ F) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) k ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyCosliceEvaluation F W hF x := pullback.lift_fst _ _ _

/-- 元の底図式の射影は、同じ分数比較によって全単体で厳密に保持される。 -/
theorem fractionCosliceBaseChange_snd {A : SSet.{u}} (k : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange F W hF x k ≫ pullback.snd _ (k ≫ F) =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) k := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange_fst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange_fst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange_snd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange_snd

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fractionCosliceBaseChange._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionCosliceBaseChange._proof_3
