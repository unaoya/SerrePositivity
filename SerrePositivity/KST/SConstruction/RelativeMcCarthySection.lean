module
public import SerrePositivity.KST.SConstruction.RelativeMcCarthyRho

/-! # 相対左 fiber の McCarthy 切断
概要：B の object S から相対左 fiber への標準切断を構成する。
方針：周囲の切断と quotient の厳密な右逆を、全成分の所属条件で持ち上げる。
規約：選択した零対象が A に入ることは基底の fiber 条件から回収する。
使われ方：相対 quotient のホモトピー逆。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- B の object S から周囲の切断へ送った族の quotient は全成分で B に入る。 -/
lemma relativeMcCarthySection_quotient_in_closed {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) {m : ℕ}
    (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌)
    (n : SimplexCategoryᵒᵖ) (x : (objectSConstruction (closedSubcategory B)).obj n) :
    ObjectSInClosed B
      ((objectSConstructionFunctor.map (closedStableInclusion B) ≫
        mcCarthyFiberSection X (relativeCofiberBaseSimplex A a) ≫
          cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x) := by
  rw [mcCarthyFiberSection_quotient]
  exact objectSClosedInclusion_mem B n x

/-- B の object S から同じ相対左 fiber への実際の McCarthy 切断。 -/
def relativeMcCarthyFiberSection {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    objectSConstruction (closedSubcategory B) ⟶ relativeCofiberSubobjectLeftFiber A B a :=
  relativeCofiberLeftFiberLift A B a
    (objectSConstructionFunctor.map (closedStableInclusion B) ≫
      mcCarthyFiberSection X (relativeCofiberBaseSimplex A a))
    (relativeMcCarthySection_quotient_in_closed A B a)

/-- 相対切断は忘却によって元の周囲の切断を厳密に回収する。 -/
lemma relativeMcCarthyFiberSection_forget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyFiberSection A B a ≫ relativeCofiberLeftFiberForget A B a =
      objectSConstructionFunctor.map (closedStableInclusion B) ≫
        mcCarthyFiberSection X (relativeCofiberBaseSimplex A a) :=
  relativeCofiberLeftFiberLift_forget _ _ _ _ _

/-- 相対切断の quotient は元の B の object S の恒等射。 -/
lemma relativeMcCarthyFiberSection_quotient {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeMcCarthyFiberSection A B a ≫ relativeCofiberLeftFiberQuotient A B a = 𝟙 _ := by
  have : Mono (closedStableInclusion B).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier B.predicate).ι)
  apply (cancel_mono (objectSConstructionFunctor.map (closedStableInclusion B))).1
  rw [Category.assoc, ← relativeCofiberLeftFiberForget_quotient, ← Category.assoc,
    relativeMcCarthyFiberSection_forget, Category.assoc, mcCarthyFiberSection_quotient]
  rfl

end SerrePositivity.KST.SConstruction
