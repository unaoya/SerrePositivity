module
public import SerrePositivity.InfinityCategories.Derived.DGFullSquareLift
public import SerrePositivity.InfinityCategories.Stable.StableVertexClosure
public import SerrePositivity.InfinityCategories.Stable.CofiberZeroSource
/-!
概要：実零対象と実 fiber・cofiber による dg 対象条件の閉性を記述する。
方針：実頂点の対象ラベルを読む。規約：h の三角性を仮定しない。
使われ方：安定閉包の全 dg 部分圏の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
/-- 実零頂点・cofiber・fiber について閉じる dg 対象条件。 -/
structure DGStableObjectProperty (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    (P : D → Prop) : Prop where
  zero (z : (dgNerve A D) _⦋0⦌) : IsZeroVertex z → P (z.obj 0)
  cofiber (t : ZeroTriangle (dgNerve A D)) : IsCofiberSequence t →
    P ((squareVertex t.square 0 0).obj 0) → P ((squareVertex t.square 1 0).obj 0) →
    P ((squareVertex t.square 1 1).obj 0)
  fiber (t : ZeroTriangle (dgNerve A D)) : IsFiberSequence t →
    P ((squareVertex t.square 1 0).obj 0) → P ((squareVertex t.square 1 1).obj 0) →
    P ((squareVertex t.square 0 0).obj 0)
/-- 安定閉包を満たす dg 対象の条件。 -/
def dgStableClosureProperty (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    (P : Set D) (x : D) : Prop := StableVertexClosure (X := dgNerve A D) (Simplex.vertex '' P)
      (Simplex.vertex x : (dgNerve A D) _⦋0⦌)
/-- 実頂点の対象ラベルを戻すと、その同じ実頂点になる。 -/
lemma dgNerve_vertex_obj (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    (z : (dgNerve A D) _⦋0⦌) : Simplex.vertex (z.obj 0) = z :=
  Simplex.vertexEquiv.symm_apply_apply z
/-- 指定対象の実安定閉包は、実零頂点と全 fiber・cofiber について閉じる。 -/
lemma dgStableClosureProperty_isStable (A : Type u) [CommRing A] (D : Type v)
    [DGCategory A D] (P : Set D) : DGStableObjectProperty A D (dgStableClosureProperty A D P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change StableVertexClosure (X := dgNerve A D) _ (Simplex.vertex (z.obj 0))
    rw [dgNerve_vertex_obj]
    exact StableVertexClosure.of_zero hz
  · intro t ht h₀ h₁
    simp only [dgStableClosureProperty, dgNerve_vertex_obj] at h₀ h₁ ⊢
    exact StableVertexClosure.of_cofiber t ht h₀ h₁
  · intro t ht h₁ h₂
    simp only [dgStableClosureProperty, dgNerve_vertex_obj] at h₁ h₂ ⊢
    exact StableVertexClosure.of_fiber t ht h₁ h₂
end SerrePositivity.InfinityCategories
