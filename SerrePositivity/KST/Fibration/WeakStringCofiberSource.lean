module
public import SerrePositivity.KST.Fibration.WeakStringVertices
public import SerrePositivity.KST.Fibration.WeakStringCofiberFamilies

/-! # 共通 cofiber 補完の始点と元の頂点評価の一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 共通補完の subobject は、元の指定辺の始点への完全評価そのものである。 -/
lemma weakStringCofiberSubobject_eq {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringCofiberExact q α ≫
      relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q) = weakStringVertexTopExact q n (α.toOrderHom 0) := by
  apply Subtype.ext
  have : Mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (sInputModel B).carrier
      (ClosedStablePredicate.top (sInputModel B)).predicate).ι)
  apply (cancel_mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val).1
  change ((weakStringCofiberExact q α).val ≫ relativeCofiberSubobjectMap _ _) ≫ _ =
    weakStringVertexTopMap q n (α.toOrderHom 0) ≫ _
  rw [Category.assoc, relativeCofiberSubobjectMap_ι, weakStringVertexTopMap_ι,
    ← Category.assoc]
  have he := congrArg (fun f : weakStringCategory q n ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj =>
    f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (weakStringCofiberFamilyInput_projection q α)
  have hp : cofiberProjection B.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (cofiberStableSubobject (sInputModel B)).val := by
    rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
    rfl
  simp only [Category.assoc] at he
  rw [hp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at he
  exact he

end SerrePositivity.KST.Fibration
