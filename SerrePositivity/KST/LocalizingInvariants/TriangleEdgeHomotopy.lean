module

public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalShape
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CurryIntervalNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowInverseControl

/-!
概要：三角形の前半・後半を辺の比較とし、全ホモトピーの等式を Arrow の等式へ移す。
方針：指定した退化写像で三角形を四角形へ写し、同じ全射の一単体を比較する。
規約：類の等式からホモトピーを選択しない。使われ方：相対三角形の二つの可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.HomotopyArrow

lemma congr {A X : SSet.{u}} {F G F' G' : A ⟶ X}
    (H : SSet.Homotopy F G) (J : SSet.Homotopy F' G') (h : H.h = J.h) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) :=
  Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (congrArg (fun k ↦ SSet.yonedaEquiv (curry k)) h)

lemma identity {A X : SSet.{u}} {F G : A ⟶ X} (H : SSet.Homotopy F G) (V : A ⟶ X)
    (h : H.h = fst A (Δ[1] : SSet.{u}) ≫ V) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V))) := by
  exact (congr H (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl V) h).trans
    (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom V))

end HomotopyArrow
namespace TriangleEdge

variable {X : SSet.{u}} (s : (Δ[2] : SSet.{u}) ⟶ X)

def post : SSet.Homotopy (stdSimplex.δ (2 : Fin 3) ≫ s) (stdSimplex.δ (1 : Fin 3) ≫ s) where
  h := SquareDiagonal.postShape ≫ s
  h₀ := by rw [← Category.assoc, SquareDiagonal.postShape_zero]; rfl
  h₁ := by rw [← Category.assoc, SquareDiagonal.postShape_one]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

def pre : SSet.Homotopy (stdSimplex.δ (1 : Fin 3) ≫ s) (stdSimplex.δ (0 : Fin 3) ≫ s) where
  h := SquareDiagonal.preShape ≫ s
  h₀ := by rw [← Category.assoc, SquareDiagonal.preShape_zero]; rfl
  h₁ := by rw [← Category.assoc, SquareDiagonal.preShape_one]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

end TriangleEdge
namespace CurryHomotopy

lemma slice_precomp_map {A B C X : SSet.{u}} {F G : C ⟶ X} (H : SSet.Homotopy F G)
    (r : A ⊗ B ⟶ C) (b : B _⦋0⦌) (k : A ⟶ C) (h : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := A) b ≫ r = k) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp r H) b).h = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp k H).h := by
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap b ▷ (Δ[1] : SSet.{u})) ≫ (r ▷ Δ[1]) ≫ H.h = (k ▷ Δ[1]) ≫ H.h
  rw [← Category.assoc, ← comp_whiskerRight, h]

end CurryHomotopy
end SerrePositivity.KST.LocalizingInvariants
