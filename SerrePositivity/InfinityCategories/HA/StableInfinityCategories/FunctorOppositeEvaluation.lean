module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SimplicialHomotopyOpposite
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOppositeHom
/-!
概要：h Fun の反転 Hom 全単射と元の頂点評価を照合する。
方針：同じ実ホモトピーを反転し、任意パラメータ族の合成表示で比較する。
規約：標準の写像空間比較と元の全関手を保持する。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 反転 Hom 全単射の頂点評価は、元の評価の反転と一致する。 -/
lemma functorOppositeHomEquiv_evaluate {A D : SSet.{u}} [Quasicategory D]
    {U V : A ⟶ D} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv U V α) (SSet.opObjEquiv.symm x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopyCategoryOpHomEquiv (U.app (Opposite.op ⦋0⦌) x) (V.app (Opposite.op ⦋0⦌) x)
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom α
  rw [← h, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorOppositeHomEquiv_homotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyCategoryOpHomEquiv_homMk]
  congr 1
  apply SSet.Truncated.Edge.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanHomotopyOpposite_vertex_edge _ _
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
