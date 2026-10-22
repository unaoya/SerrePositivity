module
public import SerrePositivity.KST.Fibration.SJointReflection
public import SerrePositivity.KST.Fibration.RelativeCofiberBaseChange
public import SerrePositivity.KST.Fibration.ObjectSinglePairComparison
public import SerrePositivity.KST.Fibration.GappedPullback

/-! # 共同反映を持つ相対 cofiber 引き戻しの元の比較

実引き戻しと零・押し出しの反映を保持し、反復 S への帰納で同じ図式を再利用する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 相対 subobject 上の元の引き戻しと、両射影による実普遍性の共同反映。 -/
structure RelativePullback (X : StableModel.{u}) (A B : ClosedStablePredicate X) where
  total : StableModel.{u}
  base : StableModel.{u}
  cofiber : total ⟶ relativeCofiberStableModel A B
  projection : total ⟶ base
  endpoint : base ⟶ closedStableModel A
  isPullback : IsPullback cofiber.val projection.val
    (relativeCofiberSubobject A B).val endpoint.val
  reflects : JointlyReflectsSData cofiber.val projection.val

/-- 元の基底射影と保持した核値 cofiber の完全な射対。 -/
def RelativePullback.pair {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) (F : StableModel.{u} ⥤ SSet.{u}) :
    F.obj D.total ⟶ F.obj D.base ⊗ F.obj (closedStableModel B) :=
  lift (F.map D.projection) (F.map (D.cofiber ≫ relativeCofiberQuotient A B))

/-- 相対引き戻しは元の object S の全単体・単体作用素も保つ。 -/
lemma RelativePullback.objectS_isPullback {X : StableModel.{u}} {A B : ClosedStablePredicate X}
    (D : RelativePullback X A B) :
    IsPullback (objectSConstructionFunctor.map D.cofiber)
      (objectSConstructionFunctor.map D.projection)
      (objectSConstructionFunctor.map (relativeCofiberSubobject A B))
      (objectSConstructionFunctor.map D.endpoint) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  exact (sConstruction_isPullback_of_gapped_reflection D.isPullback n.unop.len
    D.reflects.isGapped_iff).map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))

/-- 同じ相対引き戻しの object S の射対は、固定 K-1 と K-2 から局所化同型。 -/
lemma RelativePullback.objectPair_localized_isIso {X : StableModel.{u}}
    {A B : ClosedStablePredicate X} (D : RelativePullback X A B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.pair objectSConstructionFunctor)) := by
  unfold RelativePullback.pair
  rw [CategoryTheory.Functor.map_comp]
  exact relativeCofiberBaseChange_localized_isIso A B D.objectS_isPullback

/-- 元の相対引き戻しの同じ二成分は、単回実現で局所化同型。 -/
lemma RelativePullback.singlePair_localized_isIso {X : StableModel.{u}}
    {A B : ClosedStablePredicate X} (D : RelativePullback X A B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.pair (multiRealizationFunctor 1))) :=
  singlePair_localized_isIso_of_objectPair D.projection
    (D.cofiber ≫ relativeCofiberQuotient A B) D.objectPair_localized_isIso

end SerrePositivity.KST.Fibration
