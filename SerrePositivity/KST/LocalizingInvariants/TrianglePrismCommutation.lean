module

public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeHomotopy

/-!
概要：二辺を固定した三角形ホモトピーから、前半・後半と対角の二つの可換式を得る。
方針：退化四角形に制限して curry の自然性を適用し、固定辺の恒等を相殺する。
規約：入力は全射の固定面の式であり、h Fun の可換式を仮定しない。
使われ方：元の二三角形と標準三角形の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.TrianglePrism

variable {X : SSet.{u}} [Quasicategory X] {S T : (Δ[2] : SSet.{u}) ⟶ X}
  (H : SSet.Homotopy S T)
local notation "b₀" => stdSimplex.obj₀Equiv.symm (0 : Fin 2)
local notation "b₁" => stdSimplex.obj₀Equiv.symm (1 : Fin 2)
def firstFace := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (stdSimplex.δ (2 : Fin 3)) H

def diagonalFace := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (stdSimplex.δ (1 : Fin 3)) H

def lastFace := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (stdSimplex.δ (0 : Fin 3)) H

lemma post_commutation (e : (Δ[1] : SSet.{u}) ⟶ X)
    (hFirst : (firstFace H).h = fst (Δ[1] : SSet.{u}) Δ[1] ≫ e) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post S)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalFace H))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post T))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp SquareDiagonal.postShape H
  have hn := CurryInterval.commutation J
  have hs := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.postShape ≫ S))
    (TriangleEdge.post S) rfl
  have ht := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.postShape ≫ T))
    (TriangleEdge.post T) rfl
  have hd := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₁) (diagonalFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.postShape b₁ _ SquareDiagonal.postShape_one)
  have hi := (HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₀) (firstFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.postShape b₀ _
      SquareDiagonal.postShape_zero)).trans (HomotopyArrow.identity (firstFace H) e hFirst)
  have hl := arrow_mk_comp_congr hs hd
  have hr := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₀)))
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.postShape ≫ T))))
    hi).trans ht
  exact hl.symm.trans ((congrArg Arrow.mk hn).trans hr)

lemma pre_commutation (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hLast : (lastFace H).h = fst (Δ[1] : SSet.{u}) Δ[1] ≫ f) :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre S))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalFace H)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre T))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp SquareDiagonal.preShape H
  have hn := CurryInterval.commutation J
  have hs := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.preShape ≫ S))
    (TriangleEdge.pre S) rfl
  have ht := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.preShape ≫ T))
    (TriangleEdge.pre T) rfl
  have hd := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₀) (diagonalFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.preShape b₀ _ SquareDiagonal.preShape_zero)
  have hi := (HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₁) (lastFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.preShape b₁ _
      SquareDiagonal.preShape_one)).trans (HomotopyArrow.identity (lastFace H) f hLast)
  have hl := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_right_of_any_identity
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.preShape ≫ S))))
    (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₁)))
    hi).trans hs
  have hr := arrow_mk_comp_congr hd ht
  exact hl.symm.trans ((congrArg Arrow.mk hn).trans hr)

end SerrePositivity.KST.LocalizingInvariants.TrianglePrism
