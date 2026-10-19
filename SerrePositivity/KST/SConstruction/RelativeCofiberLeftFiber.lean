module
public import SerrePositivity.KST.SConstruction.RelativeCofiberModel
public import SerrePositivity.KST.SConstruction.McCarthyFiberEquivalence

/-! # 相対 subobject の strict 左 fiber
概要：E(A,C,B)→A の object S の左 fiber と B への quotient を構成し、全 C 内の fiber へ送る。
方針：完全関手の包含公式を object S で写し、実際の pullback の普遍性を使う。
規約：homotopy fiber や相対加法性は仮定しない。使われ方：既存の McCarthy ホモトピーの制限。
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

/-- 相対 subobject と全 C 内の subobject の object S の比較正方形。 -/
lemma relativeCofiberObjectSubobject_square {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    objectSConstructionFunctor.map (relativeCofiberSubobject A B) ≫
      objectSConstructionFunctor.map (closedStableInclusion A) =
    objectSConstructionFunctor.map (relativeCofiberInclusion A B) ≫
      objectSConstructionFunctor.map (cofiberStableSubobject X) := by
  rw [← objectSConstructionFunctor.map_comp, relativeCofiberSubobject_inclusion,
    objectSConstructionFunctor.map_comp]

/-- 相対 quotient と全 C 内の quotient の object S の比較正方形。 -/
lemma relativeCofiberObjectQuotient_square {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    objectSConstructionFunctor.map (relativeCofiberQuotient A B) ≫
      objectSConstructionFunctor.map (closedStableInclusion B) =
    objectSConstructionFunctor.map (relativeCofiberInclusion A B) ≫
      objectSConstructionFunctor.map (cofiberStableQuotient X) := by
  rw [← objectSConstructionFunctor.map_comp, relativeCofiberQuotient_inclusion,
    objectSConstructionFunctor.map_comp]

/-- A の指定単体上の相対 subobject の元の strict 左 fiber。 -/
def relativeCofiberSubobjectLeftFiber {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) : SSet.{u} :=
  simplexLeftFiber (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a

/-- 相対左 fiber の元の quotient から B の object S への射。 -/
def relativeCofiberLeftFiberQuotient {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberSubobjectLeftFiber A B a ⟶ objectSConstruction (closedSubcategory B) :=
  simplexLeftFiberProjection (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a ≫
    objectSConstructionFunctor.map (relativeCofiberQuotient A B)

/-- A の単体の全 C 内の元の像。 -/
def relativeCofiberBaseSimplex {X : StableModel.{u}} (A : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    (objectSConstruction X.carrier) _⦋m⦌ :=
  (objectSConstructionFunctor.map (closedStableInclusion A)).app (Opposite.op ⦋m⦌) a

/-- 相対左 fiber から全 C 内の McCarthy 左 fiber への元のパラメーターを保つ射。 -/
def relativeCofiberLeftFiberForget {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberSubobjectLeftFiber A B a ⟶
      cofiberSubobjectLeftFiber X (relativeCofiberBaseSimplex A a) :=
  simplexLeftFiberLift (objectSConstructionFunctor.map (cofiberStableSubobject X))
    (relativeCofiberBaseSimplex A a)
    (simplexLeftFiberProjection (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a ≫
      objectSConstructionFunctor.map (relativeCofiberInclusion A B))
    (simplexLeftFiberParameter
      (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a) (by
      rw [Category.assoc, ← relativeCofiberObjectSubobject_square, ← Category.assoc,
        simplexLeftFiber_condition, Category.assoc]
      change _ = _ ≫ SSet.yonedaEquiv.symm
        ((objectSConstructionFunctor.map (closedStableInclusion A)).app (Opposite.op ⦋m⦌) a)
      rw [SSet.yonedaEquiv_symm_comp])

/-- 相対 fiber の忘却は元の cofiber 図式の像を厳密に回収する。 -/
lemma relativeCofiberLeftFiberForget_projection {X : StableModel.{u}}
    (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberLeftFiberForget A B a ≫
      simplexLeftFiberProjection (objectSConstructionFunctor.map (cofiberStableSubobject X))
        (relativeCofiberBaseSimplex A a) =
    simplexLeftFiberProjection (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a ≫
      objectSConstructionFunctor.map (relativeCofiberInclusion A B) :=
  simplexLeftFiberLift_projection _ _ _ _ _

/-- 相対 fiber の忘却は単体パラメーターを厳密に保持する。 -/
lemma relativeCofiberLeftFiberForget_parameter {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberLeftFiberForget A B a ≫
      simplexLeftFiberParameter (objectSConstructionFunctor.map (cofiberStableSubobject X))
        (relativeCofiberBaseSimplex A a) =
    simplexLeftFiberParameter (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a :=
  simplexLeftFiberLift_parameter _ _ _ _ _

/-- 相対 quotient の忘却は元の McCarthy quotient の射と厳密に可換。 -/
lemma relativeCofiberLeftFiberForget_quotient {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    relativeCofiberLeftFiberForget A B a ≫
      cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a) =
    relativeCofiberLeftFiberQuotient A B a ≫
      objectSConstructionFunctor.map (closedStableInclusion B) := by
  rw [cofiberLeftFiberQuotient, ← Category.assoc, relativeCofiberLeftFiberForget_projection,
    Category.assoc, ← relativeCofiberObjectQuotient_square, ← Category.assoc]
  rfl

end SerrePositivity.KST.SConstruction
