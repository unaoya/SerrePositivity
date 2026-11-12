module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：二つの実作用を含む元の三角形関係を、同じ射で全体として写す。
方針：ホモトピー圏の同型の合成の保存と同じ射の合成則を使う。
規約：元の五因子と指定等式を保持。使われ方：単位三角柱の整合を値へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の五つの指定因子の三角形関係は、各因子の同じ像の間で保存される。 -/
lemma vertexIso_five_factor_relation_map {X Y : SSet.{u}} (f : X ⟶ Y)
    {a b c d e : X _⦋0⦌} (l : VertexIso a b) (n : VertexIso b c)
    (r₀ : VertexIso a d) (r₁ : VertexIso d e) (r₂ : VertexIso e c)
    (h : l ≪≫ n = r₀ ≪≫ r₁ ≪≫ r₂) :
    VertexIso.map l f ≪≫ VertexIso.map n f =
      VertexIso.map r₀ f ≪≫ VertexIso.map r₁ f ≪≫ VertexIso.map r₂ f := by
  have h' := congrArg (fun e => VertexIso.map e f) h
  simpa only [vertexIso_map_trans] using h'

/-- 元の作用を含む三角形関係は、同じ指定値の像と合成作用の像の間で保存される。 -/
lemma vertexIso_triangle_relation_map {X Y Z W : SSet.{u}}
    (g : Z ⟶ X) (k : W ⟶ X) (f : X ⟶ Y)
    {a : X _⦋0⦌} {b c : Z _⦋0⦌} {d e : W _⦋0⦌}
    (l : VertexIso a (g.app _ b)) (n : VertexIso b c)
    (r₀ : VertexIso a (k.app _ d)) (r₁ : VertexIso d e)
    (r₂ : VertexIso (k.app _ e) (g.app _ c))
    (h : l ≪≫ VertexIso.map n g = r₀ ≪≫ VertexIso.map r₁ k ≪≫ r₂) :
    VertexIso.map l f ≪≫ VertexIso.map n (g ≫ f) =
      VertexIso.map r₀ f ≪≫ VertexIso.map r₁ (k ≫ f) ≪≫ VertexIso.map r₂ f := by
  have h' := congrArg (fun e => VertexIso.map e f) h
  simpa only [vertexIso_map_trans, vertexIso_map_comp] using h'

end SerrePositivity.InfinityCategories.F2
