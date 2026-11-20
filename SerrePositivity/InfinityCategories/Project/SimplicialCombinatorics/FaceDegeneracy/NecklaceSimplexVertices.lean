module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceVertices

/-! # 元の necklace 単体と全頂点作用の回収
概要：すべての高次単体上の necklace 写像が、元の全頂点への作用で決まると示す。
方針：零単体への全頂点制限と写像の自然性を使い、標準単体の頂点判定へ戻す。
規約：元の全単体的写像を保持。使われ方：necklace 射の有限順序による解析。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet
namespace NecklaceShape


/-- 元の単体の i 番目の頂点を、同じ necklace の零単体として取り出す。 -/
def simplexVertex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ} (s : T.carrier.{u} _⦋n⦌)
    (i : Fin (n + 1)) : T.carrier.{u} _⦋0⦌ :=
  T.carrier.map (show ⦋0⦌ ⟶ ⦋n⦌ from SimplexCategory.Hom.mk (OrderHom.const (Fin 1) i)).op s

/-- 元の頂点制限は、同じ標準単体の i 番目の頂点を回収する。 -/
lemma vertexEquiv_simplexVertex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : T.carrier.{u} _⦋n⦌) (i : Fin (n + 1)) :
    T.vertexEquiv (T.simplexVertex s i) = s.val i := rfl

/-- 元の頂点制限は、同じ頂点から作った零単体そのもの。 -/
lemma simplexVertex_eq_const (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (s : T.carrier.{u} _⦋n⦌) (i : Fin (n + 1)) :
    T.simplexVertex s i = T.vertexEquiv.{u}.symm (s.val i) := by
  apply T.vertexEquiv.{u}.injective
  exact (T.vertexEquiv.{u}.apply_symm_apply (s.val i)).symm

end NecklaceShape

/-- 元の任意の単体上の necklace 射の各頂点は、同じ元の頂点作用で回収される。 -/
lemma necklaceVertexMap_simplex {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) {n : ℕ}
    (s : T.down.carrier _⦋n⦌) (i : Fin (n + 1)) :
    (f.map.app _ s).val i = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (s.val i) := by
  have h := f.map.naturality
    (show ⦋0⦌ ⟶ ⦋n⦌ from SimplexCategory.Hom.mk (OrderHom.const (Fin 1) i)).op
  have hv := congrArg (fun a => U.down.vertexEquiv.{u} (a s)) h
  change U.down.vertexEquiv (f.map.app _ (T.down.simplexVertex s i)) =
    U.down.vertexEquiv (U.down.simplexVertex (f.map.app _ s) i) at hv
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.simplexVertex_eq_const, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.vertexEquiv_simplexVertex] at hv
  exact hv.symm

/-- 元の necklace の全単体的写像の等号は、元の全頂点作用で判定できる。 -/
lemma necklaceVertexMap_injective (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (T := T) (U := U)) := by
  intro f g h
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
  apply SSet.hom_ext
  intro d
  obtain ⟨⟨n⟩⟩ := d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_simplex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_simplex]
  exact congrFun h (s.val i)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
