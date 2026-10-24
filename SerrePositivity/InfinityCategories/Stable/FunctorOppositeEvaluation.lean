module
public import SerrePositivity.InfinityCategories.Stable.SimplicialHomotopyOpposite
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 反転 Hom 全単射の頂点評価は、元の評価の反転と一致する。 -/
lemma functorOppositeHomEquiv_evaluate {A D : SSet.{u}} [Quasicategory D]
    {U V : A ⟶ D} (α : FunctorHom U V) (x : A _⦋0⦌) :
    functorHomEvaluate (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv U V α) (SSet.opObjEquiv.symm x) =
      homotopyCategoryOpHomEquiv (U.app (Opposite.op ⦋0⦌) x) (V.app (Opposite.op ⦋0⦌) x)
        (functorHomEvaluate α x) := by
  have h := functorHomHomotopy_hom α
  rw [← h, SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_homotopy,
    functorHomEvaluate_homotopy, functorHomEvaluate_homotopy,
    SerrePositivity.InfinityCategories.F1B.homotopyCategoryOpHomEquiv_homMk]
  congr 1
  apply SSet.Truncated.Edge.ext
  exact kanHomotopyOpposite_vertex_edge _ _
end SerrePositivity.InfinityCategories
