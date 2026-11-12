module
public import SerrePositivity.KST.SConstruction.RelativeLeftFiberLifting

/-! # 相対左 fiber の忘却の単射性
概要：相対左 fiber から周囲の左 fiber への射は全高次単体で単射。
方針：cofiber 図式への射影は部分圏の object S の単射で、標準単体パラメーターは保持される。
規約：ホモトピーの端点の等号を周囲から反映できる。使われ方：相対 McCarthy の厳密な端点。
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

/-- 相対左 fiber の忘却は単射。 -/
instance relativeCofiberLeftFiberForget_mono {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    {m : ℕ} (a : (objectSConstruction (closedSubcategory A)) _⦋m⦌) :
    Mono (relativeCofiberLeftFiberForget A B a) := by
  have : Mono (relativeCofiberInclusion A B).val := inferInstanceAs
    (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (cofiberDiagrams X.carrier)
      (relativeCofiberPredicate A B).predicate).ι)
  constructor
  intro K f g h
  apply simplexLeftFiber_hom_ext (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) a
  · have hp := congrArg (fun k => k ≫ simplexLeftFiberProjection
      (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (relativeCofiberBaseSimplex A a)) h
    rw [Category.assoc, Category.assoc, relativeCofiberLeftFiberForget_projection,
      ← Category.assoc, ← Category.assoc] at hp
    exact (cancel_mono (objectSConstructionFunctor.map (relativeCofiberInclusion A B))).1 hp
  · have hp := congrArg (fun k => k ≫ simplexLeftFiberParameter
      (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (relativeCofiberBaseSimplex A a)) h
    rw [Category.assoc, Category.assoc, relativeCofiberLeftFiberForget_parameter] at hp
    exact hp

end SerrePositivity.KST.SConstruction
