module
public import SerrePositivity.KST.SConstruction.CoherentTriangleFullPathValues
public import SerrePositivity.KST.SConstruction.CoherentNativeContractionEdges

/-! # 短い列の精密化の包含辺は三角形の元の合成辺
概要：長さ二の列で、元の長辺から全頂点 Path への包含を標準三角形の包含辺へ同定する。
方針：元の精密化の二端点 Path と三頂点 Path を厳密に照合する。
規約：元の Path の包含辺と単体の宇宙を保持する。
使われ方：元の K の収縮の指定成分を元の square の復号辺へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 長さ二の元の列では、精密化の Path 包含辺は標準三角形の同じ包含辺である。 -/
lemma coherentStringRefinementPathToFull_triangle_heq {I : Type u} [SmallCategory I]
    {x y : I} {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) (hs : s.length = 2) :
    HEq (nerve.edgeMk (coherentStringRefinementPathToFull (coherentArrowStringDirectTo s))).edge
      (nerve.edgeMk (coherentEndpointPathToComposite
        (show (ULift.up 0 : ULift.{u} (Fin 3)) ≤ ULift.up 1 from by decide)
        (show (ULift.up 1 : ULift.{u} (Fin 3)) ≤ ULift.up 2 from by decide))).edge := by
  rcases s with ⟨n, chain, long_edge⟩
  dsimp only at hs
  subst n
  apply heq_of_eq
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · exact coherentStringRefinementPath_directTo _
  · exact coherentTrianglePath_eq_composite _ (Set.mem_univ _)
  · apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
