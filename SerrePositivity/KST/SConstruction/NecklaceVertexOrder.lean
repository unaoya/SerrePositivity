module
public import SerrePositivity.KST.SConstruction.NecklaceEdges

/-! # 全 necklace 射の元の頂点順序の保存
概要：すべての端点保存単体的写像の頂点作用が単調であることを証明する。
方針：元のすべての隣接辺の像と、標準一単体の単調性を使う。
規約：単調性を入力仮定にしない。使われ方：joints 被覆と具体的な cubical 射。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の全 necklace 射は、元の有限頂点順序を保つ。 -/
lemma necklaceVertexMap_monotone {T U : Necklace.{u}} (f : T ⟶ U) :
    Monotone (necklaceVertexMap f) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := stdSimplex.monotone_apply
    (f.map.app _ (T.down.adjacentEdge i)).val
    (show (0 : Fin 2) ≤ Fin.last 1 from by decide)
  dsimp only at h
  rw [necklaceVertexMap_simplex, necklaceVertexMap_simplex] at h
  exact h

/-- 元の necklace 射を、その同じ単調な頂点作用として読む。 -/
def necklaceVertexOrderHom {T U : Necklace.{u}} (f : T ⟶ U) :
    T.down.Vertex →o U.down.Vertex :=
  ⟨necklaceVertexMap f, necklaceVertexMap_monotone f⟩

/-- 元の頂点順序の恒等射を回収する。 -/
lemma necklaceVertexOrderHom_id (T : Necklace.{u}) :
    necklaceVertexOrderHom (𝟙 T) = OrderHom.id := by
  apply DFunLike.ext
  intro v
  exact congrFun (necklaceVertexMap_id T) v

/-- 元の頂点順序の作用は合成を保つ。 -/
lemma necklaceVertexOrderHom_comp {T U V : Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    necklaceVertexOrderHom (f ≫ g) = (necklaceVertexOrderHom g).comp
      (necklaceVertexOrderHom f) := by
  apply DFunLike.ext
  intro v
  exact congrFun (necklaceVertexMap_comp f g) v

end SerrePositivity.KST.SConstruction
