module

public import SerrePositivity.InfinityCategories.F2.Ind.IndVertexDensity
public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyColimitValueDetection

/-!
概要：κ-filtered 保存関手間の元の比較は、Yoneda 像上で可逆なら Indκ の全対象で可逆。
方針：元の指定密度余錐を二つの保存関手で写し、同じ全ホモトピーの余極限頂点での可逆性を使う。
規約：指定した比較辺そのものの可逆性を示し、別の対象同型の存在で代用しない。
使われ方：元の制限射による同値の検出と、延長の一意性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]
  {F G : IndInfinity κ C ⟶ D}

/-- 元の自然比較は Yoneda 像上で可逆なら、同じ全密度余錐により任意の元の頂点で可逆。 -/
lemma continuousHomotopy_vertex_isInvertible
    (hF : PreservesSmallKappaFilteredColimits κ F)
    (hG : PreservesSmallKappaFilteredColimits κ G) (H : SSet.Homotopy F G)
    (hH : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C) _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge H
        ((indYoneda κ C).app (Opposite.op ⦋0⦌) x)).toTruncated)
    (v : (IndInfinity κ C) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H v).toTruncated := by
  have ht := homotopy_colimit_value_isInvertible (indVertexDensityCocone κ v)
    (indVertexDensity_image_isColimit κ v F hF) (indVertexDensity_image_isColimit κ v G hG) H
    (fun j => hH (ULift.up
      ((smallRightUnstraighteningProjection (indVertexPresheaf κ v)).app
        (Opposite.op ⦋0⦌) j.down)))
  exact Eq.mp (congrArg (fun w =>
    IsInvertibleEdge (simplicialHomotopyVertexEdge H w).toTruncated)
      (indVertexDensityCocone_vertex κ v)) ht

end SerrePositivity.InfinityCategories.F2.Ind
