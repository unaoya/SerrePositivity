module
public import SerrePositivity.InfinityCategories.Derived.DGVertexIsoOfH0

/-! # Native dg nerve の通常の h と H⁰ の比較

概要：道の商による通常のホモトピー圏を全 dg 自然な H⁰ と比較する。
方針：二切断の辺の類への比較と既存の H⁰ 比較を合成する。
規約：三角関手性はまだ主張しない。使われ方：実 cofiber の対象条件と K(D) の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 通常の h N_dg(D) と全 dg 自然な H⁰(D) の比較同値。 -/
def dgStableHomotopyEquivalence :
    SSet.hoFunctor.obj (dgNerve A D) ≌ DifferentialGraded.HomotopyCategory A D :=
  (homotopyCategoryBridge (dgNerve A D)).symm.trans (HomotopyComparison.equivalence A D)

/-- 実頂点の比較像は、同じ dg 対象の H⁰ の像。 -/
lemma dgStableHomotopyEquivalence_obj_vertex (x : D) :
    (dgStableHomotopyEquivalence A D).functor.obj
      (SSet.HomotopyCategory.mk (Simplex.vertex x)) =
        (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x) := rfl

/-- 実頂点の同型を H⁰ の同じ対象間の同型へ送る。 -/
def dgH0IsoOfVertexIso {x y : D}
    (e : VertexIso (X := dgNerve A D) (Simplex.vertex x) (Simplex.vertex y)) :
    (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) x) ≅
      (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) y) :=
  (dgStableHomotopyEquivalence A D).functor.mapIso e

end SerrePositivity.InfinityCategories
