module

public import SerrePositivity.KST.LocalizingInvariants.TrianglePrismCommutation

/-!
概要：三辺とも動く三角形 prism の前半・後半と対角の全 h Fun 自然性を示す。
方針：二つの退化四角形に curry の自然性を適用し、同じ三面へ戻す。
規約：固定辺の仮定は置かない。使われ方：後合成 prism と置換単位の比較。
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

lemma post_naturality :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post S)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalFace H))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (firstFace H)) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.post T))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp SquareDiagonal.postShape H
  have hn := CurryInterval.commutation J
  have hs := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.postShape ≫ S))
    (TriangleEdge.post S) rfl
  have ht := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.postShape ≫ T))
    (TriangleEdge.post T) rfl
  have hd := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₁) (diagonalFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.postShape b₁ _ SquareDiagonal.postShape_one)
  have hf := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₀) (firstFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.postShape b₀ _ SquareDiagonal.postShape_zero)
  exact (arrow_mk_comp_congr hs hd).symm.trans
    ((congrArg Arrow.mk hn).trans (arrow_mk_comp_congr hf ht))

lemma pre_naturality :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre S)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (lastFace H))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalFace H)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TriangleEdge.pre T))) := by
  let J := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp SquareDiagonal.preShape H
  have hn := CurryInterval.commutation J
  have hs := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.preShape ≫ S))
    (TriangleEdge.pre S) rfl
  have ht := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SquareDiagonal.preShape ≫ T))
    (TriangleEdge.pre T) rfl
  have hd := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₀) (diagonalFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.preShape b₀ _ SquareDiagonal.preShape_zero)
  have hl := HomotopyArrow.congr (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.slice J b₁) (lastFace H)
    (CurryHomotopy.slice_precomp_map H SquareDiagonal.preShape b₁ _ SquareDiagonal.preShape_one)
  exact (arrow_mk_comp_congr hs hl).symm.trans
    ((congrArg Arrow.mk hn).trans (arrow_mk_comp_congr hd ht))

end SerrePositivity.KST.LocalizingInvariants.TrianglePrism
