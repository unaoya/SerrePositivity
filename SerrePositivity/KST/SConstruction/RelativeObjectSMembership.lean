module
public import SerrePositivity.KST.SConstruction.ObjectSClosedFamilies
public import SerrePositivity.KST.SConstruction.RelativeCofiberLeftFiber

/-! # 相対 object S の所属条件
概要：E(A,C,B) の全成分条件を subobject と quotient の所属で判定する。
方針：完全な評価の object S への作用を実図式の後合成として読む。
規約：strict 左 fiber では基底 A の条件を既存の pullback 条件から回収する。
使われ方：相対左 fiber への McCarthy の族の持ち上げ。
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

/-- 相対 cofiber 値の object S の所属は subobject と quotient の全成分条件と同値。 -/
lemma objectSInRelativeCofiber_iff {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} (v : (objectSConstruction (cofiberDiagrams X.carrier)).obj n) :
    ObjectSInClosed (relativeCofiberPredicate A B) v ↔
      ObjectSInClosed A ((objectSConstructionFunctor.map (cofiberStableSubobject X)).app n v) ∧
      ObjectSInClosed B ((objectSConstructionFunctor.map (cofiberStableQuotient X)).app n v) := by
  constructor
  · intro h
    constructor
    · intro a
      rw [gappedDiagram_objectSFunctor_map]
      exact (h a).1
    · intro a
      rw [gappedDiagram_objectSFunctor_map]
      exact (h a).2
  · rintro ⟨hA, hB⟩ a
    have hAs := hA a
    have hBs := hB a
    rw [gappedDiagram_objectSFunctor_map] at hAs hBs
    exact ⟨hAs, hBs⟩

/-- A に入る基底単体の左 fiber の subobject は全成分で A に入る。 -/
lemma cofiberLeftFiberSubobject_in_closed {X : StableModel.{u}} (A : ClosedStablePredicate X)
    {m n : ℕ} (a : (objectSConstruction X.carrier) _⦋m⦌) (ha : ObjectSInClosed A a)
    (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    ObjectSInClosed A ((objectSConstructionFunctor.map (cofiberStableSubobject X)).app
      (Opposite.op ⦋n⦌) ((simplexLeftFiberProjection
        (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app
          (Opposite.op ⦋n⦌) e)) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (simplexLeftFiber_condition (objectSConstructionFunctor.map (cofiberStableSubobject X)) a)
      (Opposite.op ⦋n⦌)) e
  change (objectSConstructionFunctor.map (cofiberStableSubobject X)).app (Opposite.op ⦋n⦌)
      ((simplexLeftFiberProjection _ a).app (Opposite.op ⦋n⦌) e) =
    (SSet.yonedaEquiv.symm a).app (Opposite.op ⦋n⦌)
      ((simplexLeftFiberParameter _ a).app (Opposite.op ⦋n⦌) e) at h
  rw [h, SSet.yonedaEquiv_symm_app]
  exact ObjectSInClosed.map A ha _

/-- A に入る基底上の左 fiber では、相対所属は quotient の B 所属のみで判定できる。 -/
lemma cofiberLeftFiber_in_relative_iff {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m n : ℕ} (a : (objectSConstruction X.carrier) _⦋m⦌) (ha : ObjectSInClosed A a)
    (e : (cofiberSubobjectLeftFiber X a) _⦋n⦌) :
    ObjectSInClosed (relativeCofiberPredicate A B)
      ((simplexLeftFiberProjection
        (objectSConstructionFunctor.map (cofiberStableSubobject X)) a).app
        (Opposite.op ⦋n⦌) e) ↔
    ObjectSInClosed B ((cofiberLeftFiberQuotient X a).app (Opposite.op ⦋n⦌) e) := by
  rw [objectSInRelativeCofiber_iff]
  exact and_iff_right (cofiberLeftFiberSubobject_in_closed A a ha e)

/-- 相対 fiber の基底を忘れた単体は全成分で A に入る。 -/
lemma relativeCofiberBaseSimplex_in_closed {X : StableModel.{u}} (A : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    ObjectSInClosed A (relativeCofiberBaseSimplex A a) :=
  objectSClosedInclusion_mem A _ a

/-- 相対 fiber の quotient を忘れた単体は全成分で B に入る。 -/
lemma relativeCofiberLeftFiberForget_quotient_in_closed {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) {m n : ℕ}
    (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌)
    (e : (relativeCofiberSubobjectLeftFiber A B a) _⦋n⦌) :
    ObjectSInClosed B ((cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app
      (Opposite.op ⦋n⦌) ((relativeCofiberLeftFiberForget A B a).app (Opposite.op ⦋n⦌) e)) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (relativeCofiberLeftFiberForget_quotient A B a) (Opposite.op ⦋n⦌)) e
  change (cofiberLeftFiberQuotient X (relativeCofiberBaseSimplex A a)).app (Opposite.op ⦋n⦌)
      ((relativeCofiberLeftFiberForget A B a).app (Opposite.op ⦋n⦌) e) =
    (objectSConstructionFunctor.map (closedStableInclusion B)).app (Opposite.op ⦋n⦌)
      ((relativeCofiberLeftFiberQuotient A B a).app (Opposite.op ⦋n⦌) e) at h
  rw [h]
  exact objectSClosedInclusion_mem B _ _

end SerrePositivity.KST.SConstruction
