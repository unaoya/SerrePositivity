module
public import SerrePositivity.KST.SConstruction.CubeVertexBlocks

/-! # 因子順を保つ立方体頂点の次元移送
概要：次元の等号による移送と連結の結合・単位の評価を照合する。
方針：右ブロックで帰納し、座標を反転せず cons を保つ。
規約：移送は Fin.cast による元の座標の保持。使われ方：具体的連結積の結合同型。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 次元の等号に沿って、元の座標をそのまま保持する。 -/
def cubeVertexCast {n m : ℕ} (h : n = m) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  fun i => x (Fin.cast h.symm i)

/-- 恒等な次元移送は元の頂点。 -/
lemma cubeVertexCast_refl {n : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) : cubeVertexCast rfl x = x := rfl

/-- 次元移送は元の先頭座標と tail を保つ。 -/
lemma cubeVertexCast_cons {n m : ℕ} (h : n = m) (b : Bool) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    cubeVertexCast (congrArg Nat.succ h) (Fin.cons b x) =
      Fin.cons b (cubeVertexCast h x) := by
  cases h
  rfl

/-- 次元移送は、左右の因子を交換せず連結と可換。 -/
lemma cubeVertexCast_join {n n' m m' : ℕ} (h : n = n') (k : m = m')
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexCast (congrArg₂ Nat.add h k) (cubeVertexJoin x y) =
      cubeVertexJoin (cubeVertexCast h x) (cubeVertexCast k y) := by
  cases h
  cases k
  rfl

/-- 元の三頂点の連結は、次元の結合則に沿って同じ頂点を与える。 -/
lemma cubeVertexJoin_assoc {n m k : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (z : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k) :
    cubeVertexCast (Nat.add_assoc n m k) (cubeVertexJoin (cubeVertexJoin x y) z) =
      cubeVertexJoin x (cubeVertexJoin y z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change cubeVertexCast (congrArg Nat.succ (Nat.add_assoc n m k))
        (Fin.cons (z 0) (cubeVertexJoin (cubeVertexJoin x y) (fun j => z j.succ))) =
      Fin.cons (z 0) (cubeVertexJoin x (cubeVertexJoin y (fun j => z j.succ)))
    rw [cubeVertexCast_cons (Nat.add_assoc n m k), ih]

/-- 左側の零次元ブロックを除いた連結は元の右頂点。 -/
lemma cubeVertexJoin_zero_left {m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex 0) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexCast (Nat.zero_add m) (cubeVertexJoin x y) = y := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    change cubeVertexCast (congrArg Nat.succ (Nat.zero_add m))
      (Fin.cons (y 0) (cubeVertexJoin x (fun j => y j.succ))) = y
    rw [cubeVertexCast_cons (Nat.zero_add m), ih]
    exact Fin.cons_self_tail y

/-- 左結合した三ブロック上での一致は元の全頂点上での一致を与える。 -/
lemma cubeVertex_eq_of_tripleJoin {n m k l : ℕ}
    (f g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex ((n + m) + k) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex l)
    (h : ∀ x y z, f (cubeVertexJoin (cubeVertexJoin x y) z) =
      g (cubeVertexJoin (cubeVertexJoin x y) z)) : f = g := by
  funext v
  let a := cubeVertexLeftPart k v
  let b := cubeVertexRightPart (n + m) k v
  have hv : cubeVertexJoin
      (cubeVertexJoin (cubeVertexLeftPart m a) (cubeVertexRightPart n m a)) b = v := by
    rw [cubeVertexJoin_parts]
    exact cubeVertexJoin_parts v
  rw [← hv]
  exact h _ _ _

end SerrePositivity.KST.SConstruction
