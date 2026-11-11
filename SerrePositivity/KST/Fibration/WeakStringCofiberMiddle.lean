module
public import SerrePositivity.KST.Fibration.WeakStringCofiberSource

/-! # 元の W 辺の共通 cofiber 補完の中間評価と終点の厳密照合 -/

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

/-- E(B,B,ker q) の元の中間評価を、同じ全頂点部分圏へ制限する。 -/
def weakRelativeMiddleMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakCofiberModel q).carrier ⟶
      closedSubcategory (ClosedStablePredicate.top (sInputModel B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _
    ((relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).val ≫ (cofiberStableMiddle (sInputModel B)).val)
    (fun _ => trivial)

/-- 中間評価の同じ制限は完全関手である。 -/
def weakRelativeMiddle {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakCofiberModel q ⟶ closedStableModel (ClosedStablePredicate.top (sInputModel B)) :=
  ⟨weakRelativeMiddleMap q, by
    apply preservesCofiberData_fullSubcomplex_of_comp
      (ClosedStablePredicate.top (sInputModel B)).predicate
    change PreservesCofiberData
      ((relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val ≫ (cofiberStableMiddle (sInputModel B)).val)
    exact PreservesCofiberData.comp
      (relativeCofiberInclusion _ _).property (cofiberStableMiddle (sInputModel B)).property⟩

/-- 共通補完の中間評価は、元の指定実辺の終点評価そのものである。 -/
lemma weakStringCofiberMiddle_eq {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) :
    weakStringCofiberExact q α ≫ weakRelativeMiddle q =
      weakStringVertexTopExact q n (α.toOrderHom 1) := by
  apply Subtype.ext
  have : Mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (sInputModel B).carrier
      (ClosedStablePredicate.top (sInputModel B)).predicate).ι)
  apply (cancel_mono (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val).1
  change ((weakStringCofiberExact q α).val ≫ weakRelativeMiddleMap q) ≫ _ =
    weakStringVertexTopMap q n (α.toOrderHom 1) ≫ _
  have hm : weakRelativeMiddleMap q ≫
      (closedStableInclusion (ClosedStablePredicate.top (sInputModel B))).val =
        (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
          (kernelClosedPredicate q)).val ≫ (cofiberStableMiddle (sInputModel B)).val := rfl
  rw [Category.assoc, hm, weakStringVertexTopMap_ι, ← Category.assoc]
  have he := congrArg (fun f : weakStringCategory q n ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj =>
    f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (weakStringCofiberFamilyInput_projection q α)
  have hp : cofiberProjection B.obj ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (cofiberStableMiddle (sInputModel B)).val := by
    rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
    rfl
  simp only [Category.assoc] at he
  rw [hp, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at he
  exact he

end SerrePositivity.KST.Fibration
