module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：同じ実ホモトピーの頂点辺を回収し、全関手射の可逆性へ接続する。
方針：元の閉射・実出力分解・関手空間の点ごとの判定を使う。
規約：出力の射影性と始域の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
lemma functorHomPostcomp_homotopy_isIso_of_pointwise {X Y Z : SSet.{u}}
    [Quasicategory Z] {f g : X ⟶ Y} (H : SSet.Homotopy f g) (Q : Y ⟶ Z)
    (hH : ∀ x : X _⦋0⦌, IsInvertibleEdge
      ((simplicialHomotopyVertexEdge H x).toTruncated.map ((truncation 2).map Q))) :
    IsIso (functorHomPostcomp f g Q
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) := by
  have hi := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
    (functorHomotopyPostcomp H Q) (fun x => ?_)
  · change IsIso (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H Q))) at hi
    simpa only [functorHomPostcomp, functorHomotopyPostcomp_hom] using! hi
  · apply (isInvertibleEdge_congr (show
      (simplicialHomotopyVertexEdge (functorHomotopyPostcomp H Q) x).toTruncated.edge =
        ((simplicialHomotopyVertexEdge H x).toTruncated.map
          ((truncation 2).map Q)).edge from rfl)).mpr
    exact hH x
end SerrePositivity.InfinityCategories
