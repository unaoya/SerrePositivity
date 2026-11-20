module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceSimplicialSet

/-! # bead 条件を保つ単調写像の単体的作用
概要：有限順序上の写像から、元の necklace 全体の単体的写像を作る。
方針：各単体の全頂点に同じ順序写像を適用する。
規約：端点保存は要求しない。使われ方：wedge の包含と共有頂点への射影。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

open CategoryTheory _root_.Simplicial SSet

/-- 全単体の bead 条件を保つ順序写像の、元の実単体集合への作用。 -/
def orderMap {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s)) :
    T.carrier.{u} ⟶ U.carrier.{u} where
  app d := ↾fun s => ⟨stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk (f.comp (stdSimplex.objEquiv s.val).toOrderHom)),
    hf s.property⟩
  naturality {d e} a := by
    obtain ⟨⟨n⟩⟩ := d
    obtain ⟨⟨m⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (orderMap)


/-- 元の各単体の全頂点上で、指定した順序写像を回収する。 -/
lemma orderMap_vertex {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s))
    {n : ℕ} (s : T.carrier.{u} _⦋n⦌) (i : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap f hf).app _ s).val i = f (s.val i) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (orderMap_vertex)


/-- 定値な元の単体への作用も、同じ順序写像の定値単体。 -/
lemma orderMap_constant {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s))
    (v : T.Vertex) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.orderMap f hf).app _ (T.constantSimplex v n) = U.constantSimplex (f v) n := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (orderMap_constant)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
