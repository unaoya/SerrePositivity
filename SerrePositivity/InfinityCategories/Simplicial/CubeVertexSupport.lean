module
public import SerrePositivity.InfinityCategories.Simplicial.CubeVertexMaps
public import Mathlib.Data.Fintype.Fin

/-! # 具体的な立方体の真の座標による join 表示
概要：任意の頂点を、その真の座標に対応する一座標頂点の有限 join として回収する。
方針：真の座標の有限集合と元の一座標頂点を使い、pointwise な両向きの不等式を示す。
規約：零次元の空の support も含む。使われ方：具体的な cubical 射の有限データによる判定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 指定した一座標だけが真である、元の立方体の頂点。 -/
def cubeVertexAtom (n : ℕ) (i : Fin n) : CubeVertex n :=
  fun j => decide (j = i)

/-- 元の頂点の真の座標の有限集合。 -/
def cubeVertexSupport {n : ℕ} (x : CubeVertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

/-- 元の頂点の support への所属は、その同じ座標が真であること。 -/
lemma mem_cubeVertexSupport {n : ℕ} (x : CubeVertex n) (i : Fin n) :
    i ∈ cubeVertexSupport x ↔ x i = true := by
  simp only [cubeVertexSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- 任意の元の頂点は、その真の座標の一座標頂点の有限 join。 -/
lemma cubeVertexSupport_sup_atoms {n : ℕ} (x : CubeVertex n) :
    (cubeVertexSupport x).sup (cubeVertexAtom n) = x := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi j
    have hxi := (mem_cubeVertexSupport x i).mp hi
    by_cases h : j = i
    · subst j
      simp [cubeVertexAtom, hxi]
    · simp [cubeVertexAtom, h]
  · intro j
    cases hx : x j with
    | false => exact bot_le
    | true =>
      have hj := (mem_cubeVertexSupport x j).mpr hx
      have h := (Finset.le_sup (f := cubeVertexAtom n) hj) j
      simpa only [cubeVertexAtom, decide_true, hx] using h

end SerrePositivity.KST.SConstruction
