module
public import SerrePositivity.InfinityCategories.Core.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：両端固定の写像空間内の比較を、境界で厳密に定値な可逆 path へ送る。
方針：同じ実辺を関手空間に含め、その可逆性と fiber の境界等式を使う。
規約：境界が恒等となるのは類の等号ではなく、全 path の厳密な等号。
使われ方：元の P 比較を、同じ ν 両端を固定する全入力の相対延長へ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
  {v w : (intervalMappingSpace x y) _⦋0⦌} (e : SSet.Edge v w)

/-- 同じ両端固定の実辺を、全区間関手間の可逆 path の頂点へ送る。 -/
def nativeArrowRelativePath :
    (equivalencePath ((ihom (Δ[1] : SSet.{u})).obj X)) _⦋0⦌ :=
  equivalencePathVertex
    (e.map (vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y)))).toTruncated (by
    apply IsInvertibleEdge.map
    exact IsGroupoid.all_isIso (C := hoFunctor.obj (intervalMappingSpace x y)) _)

lemma nativeArrowRelativePath_zero :
    (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) = v.val :=
  equivalencePathVertex_zero _ _

lemma nativeArrowRelativePath_one :
    (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) = w.val :=
  equivalencePathVertex_one _ _

/-- 境界への像は全 path として元の定値 path そのもの。 -/
lemma nativeArrowRelativePath_boundary :
    (equivalencePathMap ((pre (boundary 1).ι).app X)).app
        (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) =
      (equivalencePathRefl _).app (Opposite.op ⦋0⦌)
        (functorVertex (intervalMappingBoundary x y)) := by
  let q := (pre (boundary 1).ι).app X
  let b := functorVertex (intervalMappingBoundary x y)
  let j := vertexFiberι q b
  apply Subtype.ext
  change functorVertex (SSet.yonedaEquiv.symm (e.map j).edge ≫ q) =
    functorVertex (SSet.const b)
  apply congrArg functorVertex
  change SSet.yonedaEquiv.symm (j.app (Opposite.op ⦋1⦌) e.edge) ≫ q = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories
