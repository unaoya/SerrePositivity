module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LocalObjectLimits
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPostEquivalence

/-!
概要：任意の left fibration の全錐上の切断から底図式上の切断への制限。
方針：元の全錐の右因子への制限を正規化し、底上の同値でその同値性を移す。
規約：図式の形状は任意。指定錐と元の底上の比較射を保持する。
使われ方：元の Yoneda 前層の有限余積保存を、表現可能射影の切断へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全錐上の切断を元の底図式へ制限する射。 -/
def leftFibrationConeRestriction {K E B : SSet.{u}} (p : E ⟶ B)
    {D : K ⟶ B} (c : JoinCone D) :
    relativeFunctorSpace p c.val ⟶ relativeFunctorSpace p D :=
  relativeFunctorPre p c.val (joinInr (Δ[0] : SSet.{u}) K) ≫
    eqToHom (congrArg (relativeFunctorSpace p) c.property)

/-- 全錐の切断の制限は、元の底上の比較による後合成と厳密に可換。 -/
lemma leftFibrationConeRestriction_post {K E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    {D : K ⟶ B} (c : JoinCone D) :
    relativeFunctorPost p q f hf c.val ≫ leftFibrationConeRestriction q c =
      leftFibrationConeRestriction p c ≫ relativeFunctorPost p q f hf D := by
  unfold leftFibrationConeRestriction
  rw [← Category.assoc, relativeFunctorPost_pre, Category.assoc,
    relativeFunctorPost_transport, ← Category.assoc]
  exact c.property

/-- 底上の前合成同値は、元の全錐から底への切断制限の同値性を保ち反映する。 -/
lemma leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    {K E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f)
    {D : K ⟶ B} (c : JoinCone D) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction q c) := by
  have hfull := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q f hf ef c.val
  have hbase := relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence
    p q f hf ef D
  constructor
  · intro h
    apply hfull.cancel_left
    rw [leftFibrationConeRestriction_post p q f hf c]
    exact h.comp hbase
  · intro h
    apply hbase.cancel_right
    rw [← leftFibrationConeRestriction_post p q f hf c]
    exact hfull.comp h

end SerrePositivity.InfinityCategories.HomotopyLimits
