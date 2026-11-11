module

public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberRightShape
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：全 h Fun の指定射の可逆性を、元の全頂点成分で判定する。
方針：同じ射のホモトピー代表に点ごとの可逆性判定を適用し、元の類へ戻す。
規約：別の同型の存在で指定射を置き換えない。使われ方：模型比較の単位の逆を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma isIso_of_arrow_mk_eq {B : Type u} [Category.{v} B] {x y x' y' : B}
    {f : x ⟶ y} {g : x' ⟶ y'} [IsIso g] (h : Arrow.mk f = Arrow.mk g) : IsIso f := by
  change IsIso (Arrow.mk f).hom
  rw [h]
  exact (inferInstance : IsIso g)

def functorHomEvaluateIso {A X : SSet.{u}} {F G : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G)
    (x : A _⦋0⦌) : (HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌) x) : hoFunctor.obj X) ≅
      HomotopyCategory.mk (G.app (Opposite.op ⦋0⦌) x) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom x
  inv := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.inv x
  hom_inv_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, e.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_id]
  inv_hom_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp, e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_id]

lemma functorHom_isIso_of_pointwise {A X : SSet.{u}} [Quasicategory X] {F G : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (hα : ∀ x : A _⦋0⦌, IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x)) : IsIso α := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy α
  have hh := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  have hv : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
    intro x
    change IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
    rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy, hh]
    exact hα x
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H hv
  rw [← hh]
  exact hi

end SerrePositivity.KST.LocalizingInvariants
