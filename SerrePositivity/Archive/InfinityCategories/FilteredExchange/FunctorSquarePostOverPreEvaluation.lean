module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePostOverPreEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPostOverPreSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：共有対角を持つ二面の指定比較合成を、同じ底上の射で制限する。
方針：三つの合成作用の厳密な四角形と、元の二つの指定成分の自然性を使う。
規約：元の二面・対角・値を保持。使われ方：最後の辺の比較を元の最初の全空間へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C E : SSet.{u + 1}} {F G L J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {v : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {s : SSet.Homotopy F L} {w : SSet.Homotopy L J}
  (U : FunctorCompositionTriangle a v c) (D : FunctorCompositionTriangle s w c)
  (p : C ⟶ B) (d : E ⟶ B) (t : E ⟶ C) (ht : t ≫ p = d)
local notation "R₀" => relativeFunctorOverPre (leftUnstraighteningProjection F)
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
local notation "R₃" => relativeFunctorOverPre (leftUnstraighteningProjection J)
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)

/-- 同じ底上の射の制限は、元の二面の指定比較合成の各点の値を保持する。 -/
lemma functorSquareSequentialPostComparison_overPre_app_heq
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq (VertexIso.map (((functorTriangleSequentialPostComparison D p).app x).symm ≪≫
      (functorTriangleSequentialPostComparison U p).app x) R₃)
      (((functorTriangleSequentialPostComparison D d).app ((R₀).app _ x)).symm ≪≫
        (functorTriangleSequentialPostComparison U d).app ((R₀).app _ x)) := by
  have cc := functorHomotopyRelativePost_overPre_square c p d t ht
  have cs := functorHomotopyRelativePost_overPre_square s p d t ht
  have cw := functorHomotopyRelativePost_overPre_square w p d t ht
  have ca := functorHomotopyRelativePost_overPre_square a p d t ht
  have cv := functorHomotopyRelativePost_overPre_square v p d t ht
  have hc := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) cc.w
  have hD := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) (cs.horiz_comp cw).w
  have hU := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) (ca.horiz_comp cv).w
  have eD := functorTriangleSequentialPostComparison_overPre_app_heq D p d t ht x
  have eU := functorTriangleSequentialPostComparison_overPre_app_heq U p d t ht x
  rw [vertexIso_map_trans, vertexIso_map_symm]
  exact vertexIso_trans_heq_of_heq _ _ _ _ hD hc hU
    (vertexIso_symm_heq_of_heq _ _ hc hD eD) eU

/-- 同じ制限後の射で写しても、元の二面の指定値とその制限の値を保持する。 -/
lemma functorSquareSequentialPostComparison_overPre_app_map_heq {V : SSet.{u + 1}}
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌)
    (q : relativeFunctorSpace (leftUnstraighteningProjection J) d ⟶ V) :
    HEq (VertexIso.map (VertexIso.map
      (((functorTriangleSequentialPostComparison D p).app x).symm ≪≫
        (functorTriangleSequentialPostComparison U p).app x) R₃) q)
      (VertexIso.map
        (((functorTriangleSequentialPostComparison D d).app ((R₀).app _ x)).symm ≪≫
          (functorTriangleSequentialPostComparison U d).app ((R₀).app _ x)) q) := by
  have cs := functorHomotopyRelativePost_overPre_square s p d t ht
  have cw := functorHomotopyRelativePost_overPre_square w p d t ht
  have ca := functorHomotopyRelativePost_overPre_square a p d t ht
  have cv := functorHomotopyRelativePost_overPre_square v p d t ht
  have hD := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) (cs.horiz_comp cw).w
  have hU := congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) (ca.horiz_comp cv).w
  exact vertexIso_map_heq_of_heq _ _ hD hU
    (functorSquareSequentialPostComparison_overPre_app_heq U D p d t ht x) q

end SerrePositivity.InfinityCategories.F2
