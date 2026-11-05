module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceSimplexMaps
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceSimplexVertices

/-! # 元の同じ necklace 形と全頂点による augmentation の一致
概要：元の necklace の等号移送で全頂点作用が一致すれば、元の augmentation 対象も一致。
方針：元の形等号を消去し、全高次単体の全頂点で単体写像を判定する。
規約：元の高次単体と両端を保持。使われ方：単体写像による像部分集合 bead の照合。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の形の等号移送で全頂点作用が一致する augmentation は、元の同じ対象。 -/
lemma necklaceInSimplex_eq_of_vertices {N : ℕ} {x y : (Δ[N] : SSet.{u}) _⦋0⦌}
    {T U : NecklaceIn (Δ[N] : SSet.{u}) x y} (h : T.necklace = U.necklace)
    (hv : ∀ v : T.necklace.down.Vertex,
      necklaceSimplexVertexMap T.necklace.down T.map v =
        necklaceSimplexVertexMap U.necklace.down U.map (necklaceVertexMap (eqToHom h) v)) :
    T = U := by
  obtain ⟨t, a, ha, hb⟩ := T
  obtain ⟨s, b, hc, hd⟩ := U
  change t = s at h
  subst s
  have hmap : a = b := by
    apply SSet.hom_ext
    intro d
    obtain ⟨⟨m⟩⟩ := d
    apply ConcreteCategory.hom_ext
    intro z
    apply stdSimplex.ext
    intro i
    rw [necklaceSimplexVertexMap_simplex, necklaceSimplexVertexMap_simplex]
    exact (hv (z.val i)).trans (congrArg (necklaceSimplexVertexMap t.down b)
      (congrFun (necklaceVertexMap_id t) (z.val i)))
  cases hmap
  rfl

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_eq_of_vertices := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceInSimplex_eq_of_vertices
