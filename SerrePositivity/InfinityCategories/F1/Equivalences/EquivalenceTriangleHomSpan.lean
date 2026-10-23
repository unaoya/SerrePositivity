module

public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceTriangleHomEvaluation
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomSpanSectionTransport

/-!
概要：同じ可逆三角形の Hom の三つの比較 span と元の頂点評価との厳密な接続。
方針：元の面の両端評価を同じ頂点の Hom へ正規化する。
規約：元の同じ面・元の同じ頂点評価を使用する。
使われ方：指定された元の切断による Hom 輸送の三角形則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (Y : SSet.{u}) (i : Fin 3) (j : Fin 2) (x y : (equivalenceTriangle Y) _⦋0⦌)

/-- 元の三角形の面の Hom を、元の対応する頂点の Hom へ評価する。 -/
def equivalenceTriangleHomFaceEndpoint :
    intervalMappingSpace ((equivalenceTriangleFace Y i).app _ x)
      ((equivalenceTriangleFace Y i).app _ y) ⟶
    intervalMappingSpace ((equivalenceTriangleEvaluation Y (i.succAbove j)).app _ x)
      ((equivalenceTriangleEvaluation Y (i.succAbove j)).app _ y) :=
  intervalMappingPostOfEq (equivalencePathEndpoint Y j)
    ((equivalenceTriangleFace Y i).app _ x) ((equivalenceTriangleFace Y i).app _ y)
    (congrArg (fun f : equivalenceTriangle Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) x)
      (equivalenceTriangleFace_endpoint Y i j))
    (congrArg (fun f : equivalenceTriangle Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) y)
      (equivalenceTriangleFace_endpoint Y i j))

/-- 同じ面の Hom の端点評価は全境界を持ち上げる。 -/
lemma equivalenceTriangleHomFaceEndpoint_trivialKanFibration [Quasicategory Y] :
    TrivialKanFibration (equivalenceTriangleHomFaceEndpoint Y i j x y) := by
  have : TrivialKanFibration (equivalencePathEndpoint Y j) := by
    by_cases hj : j = 0
    · subst j
      infer_instance
    · have hj' : j = 1 := Fin.ext (by
        have hlt := j.isLt
        have hn : j.val ≠ 0 := fun h ↦ hj (Fin.ext h)
        omega)
      subst j
      infer_instance
  exact intervalMappingPostOfEq_trivialKanFibration _ _ _ _ _

/-- 同じ面の Hom を端点で評価すると、元の頂点評価の同じ Hom 作用を回収する。 -/
lemma equivalenceTriangleHomFaceEndpoint_factor :
    equivalenceTriangleHomFace Y i x y ≫ equivalenceTriangleHomFaceEndpoint Y i j x y =
      equivalenceTriangleHomEvaluation Y (i.succAbove j) x y := by
  apply intervalMappingUncurry_injective
  rw [equivalenceTriangleHomFaceEndpoint, intervalMappingPostOfEq_uncurry,
    equivalenceTriangleHomFace, intervalMappingPost_universal_uncurry,
    equivalenceTriangleHomEvaluation, intervalMappingPost_universal_uncurry,
    Category.assoc, equivalenceTriangleFace_endpoint]

end SerrePositivity.InfinityCategories
