module
public import SerrePositivity.KST.SConstruction.CubeKeepInterchange

/-! # 元の順序を保つ立方体の二ブロック分解
概要：右側の座標を先に数える規約を保ち、n+m 次元の頂点を左右の二頂点へ分解する。
方針：右ブロックの次元で帰納し、元の cons と tail だけを使う。
規約：左右の入れ替えや座標反転は行わない。使われ方：具体的立方体の連結積。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の左・右頂点を同じ因子順の n+m 次元の頂点へ連結する。 -/
def cubeVertexJoin {n : ℕ} : {m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m)
  | 0, x, _ => x
  | _m + 1, x, y => Fin.cons (y 0) (cubeVertexJoin x (fun j => y j.succ))

/-- 元の右ブロックを除いて左側の頂点を回収する。 -/
def cubeVertexLeftPart {n : ℕ} : (m : ℕ) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n
  | 0, x => x
  | m + 1, x => cubeVertexLeftPart m (fun j => x j.succ)

/-- 元の右側の頂点を同じ順で回収する。 -/
def cubeVertexRightPart (n : ℕ) : (m : ℕ) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m
  | 0, _ => Fin.elim0
  | m + 1, x => Fin.cons (x 0) (cubeVertexRightPart n m (fun j => x j.succ))

/-- 連結から元の左側の頂点を厳密に回収する。 -/
lemma cubeVertexJoin_leftPart {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexLeftPart m (cubeVertexJoin x y) = x := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (fun j => y j.succ)

/-- 連結から元の右側の頂点を厳密に回収する。 -/
lemma cubeVertexJoin_rightPart {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexRightPart n m (cubeVertexJoin x y) = y := by
  induction m with
  | zero => funext j; exact Fin.elim0 j
  | succ m ih =>
    change Fin.cons (y 0)
      (cubeVertexRightPart n m (cubeVertexJoin x (fun j => y j.succ))) = y
    rw [ih]
    exact Fin.cons_self_tail y

/-- 元の頂点は左右の分解から厳密に回収される。 -/
lemma cubeVertexJoin_parts {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m)) :
    cubeVertexJoin (cubeVertexLeftPart m x) (cubeVertexRightPart n m x) = x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fin.cons (x 0) (cubeVertexJoin (cubeVertexLeftPart m (fun j => x j.succ))
      (cubeVertexRightPart n m (fun j => x j.succ))) = x
    rw [ih]
    exact Fin.cons_self_tail x

/-- 元の全頂点での二ブロック分解は、実際の同値。 -/
def cubeVertexBlockEquiv (n m : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m) ≃ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n × _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m where
  toFun x := (cubeVertexLeftPart m x, cubeVertexRightPart n m x)
  invFun p := cubeVertexJoin p.1 p.2
  left_inv := cubeVertexJoin_parts
  right_inv p := Prod.ext (cubeVertexJoin_leftPart p.1 p.2) (cubeVertexJoin_rightPart p.1 p.2)

/-- 左右の元の頂点写像の、順序を保つ二ブロック作用。 -/
def cubeVertexTensor {n p m q : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (p + q) :=
  fun x => cubeVertexJoin (f (cubeVertexLeftPart m x)) (g (cubeVertexRightPart n m x))

/-- 元の連結した頂点に対する二ブロック作用は、元の左右の作用を回収する。 -/
lemma cubeVertexTensor_join {n p m q : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexTensor f g (cubeVertexJoin x y) = cubeVertexJoin (f x) (g y) := by
  dsimp only [cubeVertexTensor]
  rw [cubeVertexJoin_leftPart, cubeVertexJoin_rightPart]

/-- 二ブロック作用は元の恒等写像を保つ。 -/
lemma cubeVertexTensor_id (n m : ℕ) :
    cubeVertexTensor (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
      (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) = _root_.id := by
  funext x
  exact cubeVertexJoin_parts x

/-- 二ブロック作用は元の関数合成を保つ。 -/
lemma cubeVertexTensor_comp {n p r m q s : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p) (f' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex r)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q) (g' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex s) :
    cubeVertexTensor (f' ∘ f) (g' ∘ g) = cubeVertexTensor f' g' ∘ cubeVertexTensor f g := by
  funext x
  exact (cubeVertexTensor_join f' g' _ _).symm

/-- 元の連結した全頂点で一致すれば、同じ二ブロック作用そのものに一致する。 -/
lemma cubeVertexTensor_eq_of_join {n p m q : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p) (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + m) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (p + q))
    (h : ∀ x y, t (cubeVertexJoin x y) = cubeVertexJoin (f x) (g y)) :
    t = cubeVertexTensor f g := by
  funext z
  exact (congrArg t (cubeVertexJoin_parts z)).symm.trans
    (h (cubeVertexLeftPart m z) (cubeVertexRightPart n m z))

end SerrePositivity.KST.SConstruction
