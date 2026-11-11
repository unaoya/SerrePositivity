module
public import SerrePositivity.KST.SConstruction.RelativeObjectSMembership

/-! # 相対左 fiber への族の持ち上げ
概要：A の基底上の周囲の左 fiber の族は、quotient が B に入れば相対左 fiber へ持ち上がる。
方針：全成分条件から object S の族を持ち上げ、包含の単射で pullback の可換性を反映する。
規約：パラメーターと周囲の族は厳密に保持する。使われ方：相対 ρ・θ と切断。
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

/-- quotient の B 所属から相対 object S 値の族を厳密に持ち上げる。 -/
def relativeCofiberFiberObjectLift {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) {K : SSet.{u}}
    (F : K ⟶ cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a))
    (hF : ∀ n (x : K.obj n), ObjectSInClosed B
      ((F ≫ cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x)) :
    K ⟶ objectSConstruction (relativeCofiberDiagrams A B) :=
  objectSClosedFamilyLift (relativeCofiberPredicate A B)
    (F ≫ simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (relativeCofiberBaseSimplex A a)) (by
        rintro ⟨⟨n⟩⟩ x
        exact (cofiberLeftFiber_in_relative_iff A B (relativeCofiberBaseSimplex A a)
          (relativeCofiberBaseSimplex_in_closed A a) (F.app (Opposite.op ⦋n⦌) x)).2
            (hF (Opposite.op ⦋n⦌) x))

/-- 相対 object S 値の持ち上げは周囲の図式への射影を厳密に回収する。 -/
lemma relativeCofiberFiberObjectLift_inclusion {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) {K : SSet.{u}}
    (F : K ⟶ cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a))
    (hF : ∀ n (x : K.obj n), ObjectSInClosed B
      ((F ≫ cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x)) :
    relativeCofiberFiberObjectLift A B a F hF ≫
      objectSConstructionFunctor.map (relativeCofiberInclusion A B) =
    F ≫ simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (relativeCofiberBaseSimplex A a) :=
  objectSClosedFamilyLift_inclusion _ _ _

/-- 周囲の左 fiber の族を元の単体パラメーターを保って相対左 fiber に持ち上げる。 -/
def relativeCofiberLeftFiberLift {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) {K : SSet.{u}}
    (F : K ⟶ cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a))
    (hF : ∀ n (x : K.obj n), ObjectSInClosed B
      ((F ≫ cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x)) :
    K ⟶ relativeCofiberSubobjectLeftFiber A B a :=
  simplexLeftFiberLift (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a
    (relativeCofiberFiberObjectLift A B a F hF)
    (F ≫ simplexLeftFiberParameter (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (relativeCofiberBaseSimplex A a)) (by
        have : Mono (closedStableInclusion A).val :=
          inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier A.predicate).ι)
        apply (cancel_mono (objectSConstructionFunctor.map (closedStableInclusion A))).1
        rw [Category.assoc, relativeCofiberObjectSubobject_square, ← Category.assoc,
          relativeCofiberFiberObjectLift_inclusion, Category.assoc, simplexLeftFiber_condition]
        change F ≫ simplexLeftFiberParameter
            (objectSConstructionFunctor.map (cofiberStableSubobject X))
            (relativeCofiberBaseSimplex A a) ≫ SSet.yonedaEquiv.symm
              ((objectSConstructionFunctor.map (closedStableInclusion A)).app
                (Opposite.op ⦋m⦌) a) = _
        rw [← SSet.yonedaEquiv_symm_comp, ← Category.assoc, ← Category.assoc])

/-- 相対左 fiber の持ち上げは周囲へ忘れると元の族そのもの。 -/
lemma relativeCofiberLeftFiberLift_forget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) {K : SSet.{u}}
    (F : K ⟶ cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a))
    (hF : ∀ n (x : K.obj n), ObjectSInClosed B
      ((F ≫ cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app n x)) :
    relativeCofiberLeftFiberLift A B a F hF ≫ relativeCofiberLeftFiberForget A B a = F := by
  apply simplexLeftFiber_hom_ext (objectSConstructionFunctor.map (cofiberStableSubobject X))
    (relativeCofiberBaseSimplex A a)
  · rw [Category.assoc, relativeCofiberLeftFiberForget_projection, ← Category.assoc,
      relativeCofiberLeftFiberLift, simplexLeftFiberLift_projection,
      relativeCofiberFiberObjectLift_inclusion]
  · rw [Category.assoc, relativeCofiberLeftFiberForget_parameter,
      relativeCofiberLeftFiberLift, simplexLeftFiberLift_parameter]

end SerrePositivity.KST.SConstruction
