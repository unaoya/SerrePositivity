module
public import SerrePositivity.KST.SConstruction.ClosedObjectSConstruction

/-! # 閉じた全部分圏への object S の族の持ち上げ
概要：全次数の全 Ar 成分の所属条件を持つ単体的な族を、部分圏の object S に持ち上げる。
方針：条件付きの部分単体集合を経由し、構成済みの厳密な同型の逆を使う。
規約：持ち上げは包含後に元の族を厳密に回収する。使われ方：相対 McCarthy のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 全成分条件を持つ族は条件付きの部分単体集合に自然に因子化する。 -/
def closedObjectSFamily {X : StableModel.{u}} (P : ClosedStablePredicate X) {K : SSet.{u}}
    (F : K ⟶ objectSConstruction X.carrier)
    (hF : ∀ n (x : K.obj n), ObjectSInClosed P (F.app n x)) :
    K ⟶ closedObjectSConstruction P where
  app n := ↾fun x => ⟨F.app n x, hF n x⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change F.app m (K.map α x) = (objectSConstruction X.carrier).map α (F.app n x)
    exact ConcreteCategory.congr_hom (F.naturality α) x

/-- 条件付き部分単体集合からの逆比較は元の包含と厳密に可換。 -/
lemma objectSClosedBackward_inclusion {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    objectSClosedBackward P ≫ objectSConstructionFunctor.map (closedStableInclusion P) =
      closedObjectSInclusion P := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  exact objectSClosedVertexLift_inclusion P v.val v.property

/-- 全成分条件を持つ任意の族を部分圏の元の object S に持ち上げる。 -/
def objectSClosedFamilyLift {X : StableModel.{u}} (P : ClosedStablePredicate X) {K : SSet.{u}}
    (F : K ⟶ objectSConstruction X.carrier)
    (hF : ∀ n (x : K.obj n), ObjectSInClosed P (F.app n x)) :
    K ⟶ objectSConstruction (closedSubcategory P) :=
  closedObjectSFamily P F hF ≫ objectSClosedBackward P

/-- 族の持ち上げは元の object S の包含を通して元の族を回収する。 -/
lemma objectSClosedFamilyLift_inclusion {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ objectSConstruction X.carrier)
    (hF : ∀ n (x : K.obj n), ObjectSInClosed P (F.app n x)) :
    objectSClosedFamilyLift P F hF ≫
      objectSConstructionFunctor.map (closedStableInclusion P) = F := by
  rw [objectSClosedFamilyLift, Category.assoc, objectSClosedBackward_inclusion]
  rfl

/-- 元の族を包含後に回収する二つの部分圏値の族は等しい。 -/
lemma objectSClosedFamilyLift_unique {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {K : SSet.{u}} (F : K ⟶ objectSConstruction X.carrier)
    (hF : ∀ n (x : K.obj n), ObjectSInClosed P (F.app n x))
    (G : K ⟶ objectSConstruction (closedSubcategory P))
    (hG : G ≫ objectSConstructionFunctor.map (closedStableInclusion P) = F) :
    G = objectSClosedFamilyLift P F hF := by
  have : Mono (closedStableInclusion P).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate).ι)
  apply (cancel_mono (objectSConstructionFunctor.map (closedStableInclusion P))).1
  rw [hG, objectSClosedFamilyLift_inclusion]

end SerrePositivity.KST.SConstruction
