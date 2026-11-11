module
public import SerrePositivity.KST.SConstruction.ObjectSClosedVertices

/-! # 全成分が閉じた部分圏に入る object S の単体的模型
概要：全 Ar 成分への条件を各次数に課した部分単体集合は、部分圏自身の object S に同型。
方針：単体ごとの持ち上げを包含の単射で自然な射に束ねる。
規約：元の図式を保持し、高次単体の条件を零次元条件に縮めない。
使われ方：相対図式値の単体ホモトピーを持ち上げる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 全 Ar 成分への所属条件が定める部分複体。 -/
def closedObjectSSubcomplex {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    (objectSConstruction X.carrier).Subcomplex where
  obj _n := {v | ObjectSInClosed P v}
  map α _ hv := ObjectSInClosed.map P hv α

/-- 全 Ar 成分が閉じた部分圏に入る object S の部分単体集合。 -/
def closedObjectSConstruction {X : StableModel.{u}} (P : ClosedStablePredicate X) : SSet.{u} :=
  closedObjectSSubcomplex P

/-- 全成分の条件を忘れる包含。 -/
def closedObjectSInclusion {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    closedObjectSConstruction P ⟶ objectSConstruction X.carrier where
  app _ := ↾Subtype.val
  naturality {_n _m} _α := rfl

/-- 部分圏の object S は全成分の所属条件を持つ部分単体集合へ送られる。 -/
def objectSClosedForward {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    objectSConstruction (closedSubcategory P) ⟶ closedObjectSConstruction P :=
  Subcomplex.lift (objectSConstructionFunctor.map (closedStableInclusion P)) (by
    intro n v hv
    obtain ⟨w, rfl⟩ := hv
    exact objectSClosedInclusion_mem P n w)

/-- 全成分の所属条件を持つ単体の持ち上げは自然な単体的射を与える。 -/
def objectSClosedBackward {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    closedObjectSConstruction P ⟶ objectSConstruction (closedSubcategory P) where
  app _ := ↾fun v => objectSClosedVertexLift P v.val v.property
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro v
    have : Mono (closedStableInclusion P).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate).ι)
    apply objectSConstructionFunctor_map_injective (closedStableInclusion P) m
    change (objectSConstructionFunctor.map (closedStableInclusion P)).app m
        (objectSClosedVertexLift P ((objectSConstruction X.carrier).map α v.val) _) =
      (objectSConstructionFunctor.map (closedStableInclusion P)).app m
        ((objectSConstruction (closedSubcategory P)).map α
          (objectSClosedVertexLift P v.val v.property))
    rw [objectSClosedVertexLift_inclusion]
    have h := ConcreteCategory.congr_hom
      ((objectSConstructionFunctor.map (closedStableInclusion P)).naturality α)
        (objectSClosedVertexLift P v.val v.property)
    change (objectSConstructionFunctor.map (closedStableInclusion P)).app m
        ((objectSConstruction (closedSubcategory P)).map α
          (objectSClosedVertexLift P v.val v.property)) =
      (objectSConstruction X.carrier).map α
        ((objectSConstructionFunctor.map (closedStableInclusion P)).app n
          (objectSClosedVertexLift P v.val v.property)) at h
    rw [objectSClosedVertexLift_inclusion] at h
    exact h.symm

/-- 全成分の所属条件の模型と元の部分圏の object S は厳密に同型。 -/
def objectSClosedIso {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    objectSConstruction (closedSubcategory P) ≅ closedObjectSConstruction P where
  hom := objectSClosedForward P
  inv := objectSClosedBackward P
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    have : Mono (closedStableInclusion P).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate).ι)
    apply objectSConstructionFunctor_map_injective (closedStableInclusion P) n
    exact objectSClosedVertexLift_inclusion P _ _
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    exact objectSClosedVertexLift_inclusion P _ _

/-- 部分模型への順比較を包含に合成すると元の object S の包含。 -/
lemma objectSClosedForward_inclusion {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    objectSClosedForward P ≫ closedObjectSInclusion P =
      objectSConstructionFunctor.map (closedStableInclusion P) := rfl

end SerrePositivity.KST.SConstruction
