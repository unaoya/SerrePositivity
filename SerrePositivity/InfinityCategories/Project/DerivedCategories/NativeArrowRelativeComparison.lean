module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
  {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) _⦋0⦌} (e : SSet.Edge v w)

/-- 同じ両端固定の実辺を、全区間関手間の可逆 path の頂点へ送る。 -/
def nativeArrowRelativePath :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom (Δ[1] : SSet.{u})).obj X)) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex
    (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)))).toTruncated (by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.map
    exact IsGroupoid.all_isIso (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)) _)

lemma nativeArrowRelativePath_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) = v.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_zero _ _

lemma nativeArrowRelativePath_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) = w.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_one _ _

/-- 境界への像は全 path として元の定値 path そのもの。 -/
lemma nativeArrowRelativePath_boundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre (boundary 1).ι).app X)).app
        (Opposite.op ⦋0⦌) (nativeArrowRelativePath e) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl _).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) := by
  let q := (pre (boundary 1).ι).app X
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (e.map j).edge ≫ q) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b)
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
  change SSet.yonedaEquiv.symm (j.app (Opposite.op ⦋1⦌) e.edge) ≫ q = _
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
